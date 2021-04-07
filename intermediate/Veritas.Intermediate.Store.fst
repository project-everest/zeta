module Veritas.Intermediate.Store
open FStar.Classical

let update_slot #vcfg (st:vstore_raw vcfg) (s:slot_id vcfg) (e:vstore_entry vcfg)
  : vstore_raw _
  = Seq.upd st s (Some e)

let sds vcfg = slot_id vcfg & bin_tree_dir & slot_id vcfg

let is_edge #vcfg st (e:sds vcfg) =
  let s1,d,s2 = e in
  inuse_slot st s1 && points_to_dir st s1 d s2

noeq type update_val_param (vcfg: verifier_config) =
  | UVP: st: vstore vcfg ->
         s: inuse_slot_id st ->
         v: value_type_of (stored_key st s) -> update_val_param vcfg

let uvp_slot #vcfg (uvp: update_val_param vcfg): slot_id vcfg =
  UVP?.s uvp

let uvp_val #vcfg (uvp: update_val_param vcfg) =
  UVP?.v uvp

let apply_update_val #vcfg (uvp: update_val_param vcfg) =
  match uvp with
  | UVP st s v ->
    let VStoreE k v' am lp rp p = get_inuse_slot st s in
    let e' = VStoreE k v am lp rp p in
    update_slot st s e'

let uvp_store_pre #vcfg (uvp: update_val_param vcfg) =
  UVP?.st uvp

let uvp_store_post #vcfg (uvp: update_val_param vcfg) =
  apply_update_val uvp

///  The edges are unchanged after update value
///
let uvp_edges_unchanged #vcfg uvp e
  : Lemma (is_edge (uvp_store_pre #vcfg uvp) e =
           is_edge (uvp_store_post uvp) e) = ()

///  Each slot except the updated slot remains unchanged
///
let uvp_identical_except #vcfg uvp
  : Lemma (ensures (identical_except (uvp_store_pre uvp) (uvp_store_post uvp) (uvp_slot uvp)))
          [SMTPat (apply_update_val #vcfg uvp)]
  = ()

let lemma_points_to_inuse_update_val #vcfg uvp
  : Lemma (ensures (points_to_inuse (uvp_store_post uvp)))
          [SMTPat (apply_update_val #vcfg uvp)] =
  let stp = uvp_store_pre uvp in
  let stn = uvp_store_post uvp in
  let aux s1 s2
    : Lemma (ensures (points_to_inuse_local stn s1 s2))
            [SMTPat (points_to_inuse_local stn s1 s2)] =
    assert(points_to_inuse_local stp s1 s2);
    ()
  in
  ()

let lemma_parent_props_update_val #vcfg uvp
  : Lemma (ensures (parent_props (uvp_store_post uvp)))
          [SMTPat (apply_update_val #vcfg uvp)] =
  let stp = uvp_store_pre uvp in
  let stn = uvp_store_post uvp in
  let aux s1
    : Lemma (ensures (parent_props_local stn s1))
            [SMTPat (parent_props_local stn s1)] =
    assert(parent_props_local stp s1);
    ()
  in
  ()

let lemma_madd_props_update_val #vcfg uvp
  : Lemma (ensures (madd_props (uvp_store_post uvp)))
          [SMTPat (apply_update_val #vcfg uvp)] =
  let stp = uvp_store_pre uvp in
  let stn = uvp_store_post uvp in
  let aux s1
    : Lemma (ensures (madd_props_local stn s1))
            [SMTPat (madd_props_local stn s1)] =
    assert(madd_props_local stp s1);
    ()
  in
  ()

let lemma_no_self_edge_update_val #vcfg uvp
  : Lemma (ensures (no_self_edge (uvp_store_post uvp)))
          [SMTPat (apply_update_val #vcfg uvp)] =
  let stp = uvp_store_pre uvp in
  let stn = uvp_store_post uvp in
  let aux s1
    : Lemma (ensures (no_self_edge_local stn s1))
            [SMTPat (no_self_edge_local stn s1)] =
    assert(no_self_edge_local stp s1);
    ()
  in
  ()

let update_value
  (#vcfg:_)
  (st:vstore vcfg)
  (s:inuse_slot_id st)
  (v:value_type_of (stored_key st s))
  : Tot (st':vstore vcfg {identical_except st st' s /\
                          inuse_slot st' s /\
                          v = stored_value st' s /\
                          (let VStoreE k1 _ am1 ld1 rd1 p1 = get_inuse_slot st s in
                           let VStoreE k2 _ am2 ld2 rd2 p2 = get_inuse_slot st' s in
                           k1 = k2 /\ am1 = am2 /\ ld1 = ld2 /\ rd1 = rd2 /\ p1 = p2)}) =
  let uvp = UVP st s v in
  apply_update_val uvp

noeq type madd_param (vcfg: verifier_config) =
  | MAP:   st: vstore vcfg ->
           s:empty_slot_id st ->
           k:key -> v:value_type_of k ->
           s':merkle_slot_id st ->
           d:bin_tree_dir {points_to_none st s' d} -> madd_param vcfg

let map_slot #vcfg (map: madd_param vcfg) =
  MAP?.s map

let map_key #vcfg (map: madd_param vcfg) =
  MAP?.k map

let map_val #vcfg (map: madd_param vcfg) =
  MAP?.v map

let map_dir #vcfg (map: madd_param vcfg) =
  MAP?.d map

let map_anc_slot #vcfg (map: madd_param vcfg) =
  MAP?.s' map

let apply_map #vcfg (map: madd_param vcfg) =
  match map with
  | MAP st s k v s' d ->
    let p = (map_anc_slot map), (map_dir map) in
    let e = VStoreE k v Spec.MAdd None None (Some p) in
    let st = update_slot st s e in
    let VStoreE k' v' am' l' r' p' = get_inuse_slot st s' in
    assert(None == (if d = Left then l' else r'));

    if d = Left then
      update_slot st s' (VStoreE k' v' am' (Some s) r' p')
    else
      update_slot st s' (VStoreE k' v' am' l' (Some s) p')

let map_store_pre #vcfg (map: madd_param vcfg) =
  MAP?.st map

let map_store_post #vcfg map =
  apply_map #vcfg map

///  The new edge added by the map
///
let map_new_edge #vcfg (map: madd_param vcfg): sds vcfg =
  (map_anc_slot map), (map_dir map), (map_slot map)

///  All slots except the two referenced slot in madd are unaffected by the operation
///
let map_identical_except #vcfg map
  : Lemma (ensures (identical_except2 (map_store_pre map) (map_store_post map)
                                      (map_slot map) (map_anc_slot map)))
          [SMTPat (apply_map #vcfg map)] = ()

///  Every edge in the store before madd is in the store after
///
let map_pre_edges_in_post #vcfg map e
  : Lemma (requires (is_edge (map_store_pre #vcfg map) e))
          (ensures (is_edge (map_store_post map) e)) = ()

///  Every edge in post except for the new edge is in pre
///
let map_post_edge_in_pre #vcfg map e
  : Lemma (requires (e <> map_new_edge #vcfg map /\
                     is_edge (map_store_post map) e))
          (ensures (is_edge (map_store_pre map) e)) = ()

let pointed_dir #vcfg (st: vstore_raw vcfg) s1 (s2: slot_id vcfg { points_to st s1 s2}) =
  if points_to_dir st s1 Left s2 then Left else Right

let lemma_madd_to_store_points_to_inuse #vcfg map
  : Lemma (ensures (points_to_inuse (map_store_post map)))
          [SMTPat (apply_map #vcfg map)] =
  let stp = map_store_pre map in
  let stn = map_store_post map in

  let aux s1 s2
    : Lemma (ensures (points_to_inuse_local stn s1 s2))
            [SMTPat (points_to_inuse_local stn s1 s2)] =
    assert(points_to_inuse_local stp s1 s2);
    if not (points_to stn s1 s2) then ()
    else (
      let d2 = pointed_dir stn s1 s2 in
      assert(points_to_dir stn s1 d2 s2);
      (* added slot does not point to anything *)
      assert(s1 <> map_slot map);
      if s1 = map_anc_slot map then ()
      else ()
    )
  in
  ()

let lemma_madd_to_store_parent_props #vcfg map
  : Lemma (ensures (parent_props (map_store_post map)))
          [SMTPat (apply_map #vcfg map)] =
  let stp = map_store_pre map in
  let stn = map_store_post map in

  let aux s1 : Lemma (ensures (parent_props_local stn s1)) [SMTPat (parent_props_local stn s1)] =
    assert(parent_props_local stp s1);
    if empty_slot stn s1 || not (has_parent stn s1) then ()
    else if s1 = map_slot map then ()
    else ()
  in
  ()

let lemma_madd_to_store_no_self_edge #vcfg map
  : Lemma (ensures (no_self_edge (map_store_post map)))
          [SMTPat (apply_map #vcfg map)] =
  let stp = map_store_pre map in
  let stn = map_store_post map in

  let aux s1 : Lemma (ensures (no_self_edge_local stn s1)) [SMTPat (no_self_edge_local stn s1)] =
    assert(no_self_edge_local stp s1);
    if not (points_to stn s1 s1) then ()
    else if s1 = map_anc_slot map then
      ()
    else ()
  in
  ()

let lemma_madd_to_store_madd_props #vcfg map
  : Lemma (ensures (madd_props (map_store_post map)))
          [SMTPat (apply_map #vcfg map)] =
  let stp = map_store_pre map in
  let stn = map_store_post map in
  let aux s1 : Lemma (ensures (madd_props_local stn s1)) [SMTPat (madd_props_local stn s1)] =
    assert(madd_props_local stp s1);
    if s1 = map_slot map then
      ()
    else ()
  in
  ()

let madd_to_store
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:empty_slot_id st)
  (k:key) (v:value_type_of k)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_none st s' d})
  : Tot (st':vstore vcfg{let od = other_dir d in
                         identical_except2 st st' s s' /\     // st and st' are identical except at s, s'

                         // nothing changes in slot s' except it now points to s in direction d
                         inuse_slot st' s' /\
                         stored_key st' s' = stored_key st s' /\
                         stored_value st' s' = stored_value st s' /\
                         add_method_of st' s' = add_method_of st s' /\
                         points_to_dir st' s' d s /\
                         points_to_info st' s' od = points_to_info st s' od /\

                         // slot s contains (k, v, MAdd) and points to nothing
                         inuse_slot st' s /\
                         get_inuse_slot st' s = VStoreE k v Spec.MAdd None None (Some (s',d))
                         }) =
  let map = MAP st s k v s' d in
  apply_map map

noeq type madd_split_param (vcfg: verifier_config) =
  | MSP: st: vstore vcfg ->
         s: empty_slot_id st ->
         k: key ->
         v: value_type_of k ->
         s':merkle_slot_id st ->
         d:bin_tree_dir {points_to_some_slot st s' d} ->
         d2:bin_tree_dir -> madd_split_param vcfg

let msp_store_pre #vcfg (msp: madd_split_param vcfg) =
  MSP?.st msp

let msp_anc_slot #vcfg (msp: madd_split_param vcfg) =
  MSP?.s' msp

let msp_slot #vcfg (msp: madd_split_param vcfg) =
  MSP?.s msp

let msp_dir #vcfg (msp: madd_split_param vcfg) =
  MSP?.d msp

let msp_dir2 #vcfg (msp: madd_split_param vcfg) =
  MSP?.d2 msp

let msp_desc_slot #vcfg (msp: madd_split_param vcfg) =
  let st = msp_store_pre msp in
  let s' = msp_anc_slot msp in
  let d = msp_dir msp in
  pointed_slot st s' d

let msp_desc_slot_inuse #vcfg (msp: madd_split_param vcfg)
  : Lemma (ensures (inuse_slot (msp_store_pre msp) (msp_desc_slot msp))) =
  assert(points_to (msp_store_pre msp) (msp_anc_slot msp) (msp_desc_slot msp));
  assert(points_to_inuse_local (msp_store_pre msp) (msp_anc_slot msp) (msp_desc_slot msp));
  ()

let apply_msp #vcfg (msp: madd_split_param vcfg) =
  match msp with
  | MSP st s k v s' d d2 ->
    let s2 = msp_desc_slot msp in
    let VStoreE k' v' am' l' r' p' = get_inuse_slot st s' in
    let p = s',d in
    let e = (if d2 = Left then
               VStoreE k v Spec.MAdd (Some s2) None (Some p)
             else
               VStoreE k v Spec.MAdd None (Some s2) (Some p)) in
    let st = update_slot st s e in

    let e' = (if d = Left then
                VStoreE k' v' am' (Some s) r' p'
              else
                VStoreE k' v' am' l' (Some s) p') in
    let st = update_slot st s' e' in
    msp_desc_slot_inuse msp;
    let VStoreE k2 v2 am2 l2 r2 p2 = get_inuse_slot st s2 in
    let p2new = s,d2 in
    let e2 = VStoreE k2 v2 am2 l2 r2 (Some p2new) in
    update_slot st s2 e2

let msp_store_post #vcfg (msp: madd_split_param vcfg) =
  apply_msp msp

let lemma_madd_to_store_split_identical_except #vcfg msp
  : Lemma (ensures (identical_except3 (msp_store_pre msp) (msp_store_post msp)
                                      (msp_slot msp) (msp_anc_slot msp) (msp_desc_slot msp)))
          [SMTPat (apply_msp #vcfg msp)] =
  let stp = msp_store_pre msp in
  let stn = msp_store_post msp in
  let aux s1: Lemma (ensures (s1 <> msp_slot msp ==>
                              s1 <> msp_anc_slot msp ==>
                              s1 <> msp_desc_slot msp ==>
                              get_slot stp s1 = get_slot stn s1)) =

    if s1 = msp_slot msp then ()
    else if s1 = msp_anc_slot msp then ()
    else if s1 = msp_desc_slot msp then ()
    else (
      (* TODO: Ugly hack!!
       * this is a cut-n-paste of the definition of apply_msp
       * for some reason the proof fails without the cut-n-paste and the assert
       * that follow. Might be something to do with definition expansion???
       * seq.upd needs to be expanded three times - everything works fine when we only
       * change 2 slots *)
       // BEGIN cut-n-paste
     match msp with
     | MSP st s k v s' d d2 ->
       let s2 = msp_desc_slot msp in
        let stinit = st in
      let VStoreE k' v' am' l' r' p' = get_inuse_slot st s' in
      let p = s',d in
      let e = (if d2 = Left then
               VStoreE k v Spec.MAdd (Some s2) None (Some p)
             else
               VStoreE k v Spec.MAdd None (Some s2) (Some p)) in
        let st = update_slot st s e in

      let e' = (if d = Left then
                VStoreE k' v' am' (Some s) r' p'
              else
                VStoreE k' v' am' l' (Some s) p') in
        let st = update_slot st s' e' in
      msp_desc_slot_inuse msp;
      let VStoreE k2 v2 am2 l2 r2 p2 = get_inuse_slot st s2 in
      let p2new = s,d2 in
      let e2 = VStoreE k2 v2 am2 l2 r2 (Some p2new) in
      let st = update_slot st s2 e2 in
      // end cut-n-paste
      assert(st == stn);
      assert(stinit == stp);
      assert(get_slot stp s1 = get_slot stn s1);
      ()
    )
  in
  forall_intro aux;
  ()

let is_nonedge #vcfg st (e: sds vcfg) =
  not (is_edge st e)

//#push-options "--z3rlimit_factor 3"
#push-options "--max_fuel 5 --max_ifuel 5 --z3rlimit_factor 5"

let msp_edge_post1 #vcfg msp: (e:sds vcfg {is_edge (msp_store_post msp) e}) =
  match msp with
  | MSP _ s _ _ s' d _ -> s',d,s

#pop-options

let msp_edge_post2 #vcfg msp: (e: sds vcfg {is_edge (msp_store_post msp) e}) =
  let MSP _ s _ _ _ _ d2 = msp in
  s,d2, (msp_desc_slot msp)

let msp_edge_pre1 #vcfg msp: (e: sds vcfg {is_edge (msp_store_pre msp) e}) =
  msp_anc_slot msp, msp_dir msp, msp_desc_slot msp

(* any edge in pre that is not pre1, is an edge in post *)
let msp_edge_in_pre_is_edge_in_post #vcfg msp e:
  Lemma (requires (let st' = msp_store_pre msp in
                   is_edge st' e /\ e <> msp_edge_pre1 #vcfg msp))
        (ensures (let st = msp_store_post msp in
                  is_edge st e)) = ()

let msp_edge_in_post_is_edge_pre #vcfg msp e:
  Lemma (requires (let st = msp_store_post msp in
                   is_edge st e /\ e <> msp_edge_post1 #vcfg msp /\ e <> msp_edge_post2 msp))
        (ensures (let st' = msp_store_pre msp in
                  is_edge st' e)) = ()

let msp_edge_pre1_not_edge_post #vcfg msp:
  Lemma (ensures (is_nonedge (msp_store_post msp) (msp_edge_pre1 #vcfg msp))) = ()

let msp_edge_post12_not_edge_pre #vcfg msp:
  Lemma (ensures (is_nonedge (msp_store_pre msp) (msp_edge_post1 #vcfg msp) /\
                  is_nonedge (msp_store_pre msp) (msp_edge_post2 msp))) = ()

(* added slot never equals to descendant slot *)
let msp_desc_slot_not_added_slot #vcfg msp:
  Lemma (ensures (msp_slot #vcfg msp <> msp_desc_slot msp))
        [SMTPat (msp_facts msp)]
  =
  let s = msp_slot msp in
  let s2 = msp_desc_slot msp in
  let s' = msp_anc_slot msp in
  assert(points_to_inuse_local (msp_store_pre msp)  s' s2);
  ()

let msp_anc_slot_not_added_slot #vcfg msp:
  Lemma (ensures (msp_slot #vcfg msp <> msp_anc_slot msp)) =
  ()

let msp_anc_slot_not_desc_slot #vcfg msp:
  Lemma (ensures (msp_anc_slot #vcfg msp <> msp_desc_slot msp)) =
  assert(no_self_edge_local (msp_store_pre msp) (msp_anc_slot msp));
  ()

(* before the add, nothing points to the added slot *)
let msp_nothing_points_to_added_slot #vcfg msp s d:
  Lemma (ensures (is_nonedge (msp_store_pre msp) (s, d, (msp_slot #vcfg msp)))) =
  assert(points_to_inuse_local (msp_store_pre msp) s (msp_slot msp));
  ()

let msp_points_to_added_slot #vcfg msp s1 d1:
  Lemma (ensures (let st = msp_store_post msp in
                  let s = msp_slot msp in
                  let e = s1,d1,s in
                  is_edge st e ==> e = msp_edge_post1 #vcfg msp)) =
  let st = msp_store_post msp in
  let s = msp_slot msp in
  let e = s1,d1,s in
  let e1 = msp_edge_post1 msp in
  let e2 = msp_edge_post2 msp in
  msp_desc_slot_not_added_slot msp;
  assert(e <> e2);
  if not (is_edge st e) then ()
  else if e1 = e then ()
  else (
    (* (s1,d,s) is an edge before add *)
    msp_edge_in_post_is_edge_pre msp e;
    (* which contradicts, that nothing points to s in pre *)
    msp_nothing_points_to_added_slot msp s1 d1
  )

let msp_added_slot_points_to #vcfg msp s1 d1:
  Lemma (ensures (let st = msp_store_post msp in
                  let s = msp_slot msp in
                  let e = s,d1,s1 in
                  is_edge st e ==> e = msp_edge_post2 #vcfg msp)) = ()

let msp_points_to_desc_slot #vcfg msp s1 d1:
  Lemma (ensures (let st = msp_store_post msp in
                  let sd = msp_desc_slot msp in
                  let e = s1,d1,sd in
                  is_edge st e ==> e = msp_edge_post2 #vcfg msp)) =
  let st' = msp_store_pre msp in
  let st = msp_store_post msp in
  let sd = msp_desc_slot msp in
  let e = s1,d1,sd in
  let d = msp_dir msp in
  let s' = msp_anc_slot msp in
  if not (is_edge st e) then ()
  else if e = msp_edge_post2 msp then ()
  else if s1 = s' then (
    msp_desc_slot_not_added_slot msp;
    assert(d1 <> msp_dir msp);
    assert(e <> msp_edge_post1 msp);
    msp_edge_in_post_is_edge_pre msp e;
    assert(points_to_dir st' s' d sd);
    assert(points_to_dir st' s' d1 sd);
    assert(points_to_uniq_local st' s' s' sd);
    ()
  )
  else (
    assert(get_slot st' s1 = get_slot st s1);
    assert(points_to_dir st' s1 d1 sd);
    assert(points_to_dir st' s' d sd);
    assert(points_to_uniq_local st' s' s1 sd);
    ()
  )

let lemma_madd_to_store_split_points_to_inuse
  #vcfg
  (st: vstore vcfg)
  (s:empty_slot_id st)
  (k:key) (v:value_type_of k)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_some_slot st s' d})
  (d2:bin_tree_dir)
  : Lemma (ensures (let st' = madd_to_store_split_raw st s k v s' d d2 in
                    points_to_inuse st'))
          [SMTPat (madd_to_store_split_raw st s k v s' d d2)] =
  let msp = MSP st s k v s' d d2 in
  let st' = madd_to_store_split_raw st s k v s' d d2 in
  let aux (s1 s2: slot_id _)
    : Lemma (ensures (points_to_inuse_local st' s1 s2))
            [SMTPat (points_to_inuse_local st' s1 s2)] =
    assert(points_to_inuse_local st s1 s2);
    if not (points_to st' s1 s2) then ()
    else (
      let d12 = pointed_dir st' s1 s2 in
      if s1 = s then (
        if d12 = d2 then (
          assert(points_to_inuse_local st s' s2);
          msp_added_slot_points_to msp s2 d2;
          assert(no_self_edge_local st s');
          ()
        )
        else ()
      )
      else if s1 = s' then ()
      else (
        assert(points_to_dir st s1 d12 s2);
        assert(inuse_slot st s2);
        ()
      )
    )
  in
  ()

let lemma_madd_to_store_split_points_to_unique
  #vcfg
  (st: vstore vcfg)
  (s:empty_slot_id st)
  (k:key) (v:value_type_of k)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_some_slot st s' d})
  (d2:bin_tree_dir)
  : Lemma (ensures (let st' = madd_to_store_split_raw st s k v s' d d2 in
                    points_to_uniq st'))
          [SMTPat (madd_to_store_split_raw st s k v s' d d2)] =
  let msp = MSP st s k v s' d d2 in
  let st' = madd_to_store_split_raw st s k v s' d d2 in
  let aux (s1 s2 s3:_):
    Lemma (ensures (points_to_uniq_local st' s1 s2 s3))
          [SMTPat (points_to_uniq_local st' s1 s2 s3)] =
    let od = other_dir d in
    assert(points_to_uniq_local st s1 s2 s3);
    if points_to_uniq_local st' s1 s2 s3 then ()
    else if s3 = s then (
      let d1 = pointed_dir st' s1 s in
      let d2 = pointed_dir st' s2 s in

      msp_points_to_added_slot msp s1 d1;
      msp_points_to_added_slot msp s2 d2;

      assert(s1 = s2 /\ d1 = d2);
      assert(points_to_dir st' s1 Left s && points_to_dir st' s1 Right s);
      if d1 = Left then
        msp_points_to_added_slot msp s1 Right
      else
        msp_points_to_added_slot msp s1 Left
    )
    else if s3 = s' then (
      let d13 = pointed_dir st' s1 s3 in
      let d23 = pointed_dir st' s2 s3 in
      let e13 = s1,d13,s3 in
      let e23 = s2,d23,s3 in
      assert(is_edge st' e13 /\ is_edge st' e23);
      assert(e13 <> msp_edge_post1 msp);
      assert(e23 <> msp_edge_post1 msp);
      msp_anc_slot_not_desc_slot msp;
      assert(e13 <> msp_edge_post2 msp);
      assert(e23 <> msp_edge_post2 msp);
      msp_edge_in_post_is_edge_pre msp e13;
      msp_edge_in_post_is_edge_pre msp e23;
      ()
    )
    else if s3 = msp_desc_slot msp then (
      let d13 = pointed_dir st' s1 s3 in
      let d23 = pointed_dir st' s2 s3 in
      let e13 = s1,d13,s3 in
      let e23 = s2,d23,s3 in

      msp_points_to_desc_slot msp s1 d13;
      msp_points_to_desc_slot msp s2 d23;
      assert(s1 = s2 /\ d13 = d23);
      assert(s1 = s);

      ()
    )
    else (
      let d13 = pointed_dir st' s1 s3 in
      let d23 = pointed_dir st' s2 s3 in
      let e13 = s1,d13,s3 in
      let e23 = s2,d23,s3 in
      assert(e13 <> msp_edge_post2 msp);
      assert(e13 <> msp_edge_post1 msp);
      msp_edge_in_post_is_edge_pre msp e13;
      msp_edge_in_post_is_edge_pre msp e23;

      ()
    )


  in
  ()

let madd_to_store_split_pointed_to_inv_local
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:empty_slot_id st)
  (k:key) (v:value_type_of k)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_some_slot st s' d})
  (d2:bin_tree_dir)
  (s2: slot_id vcfg)
  : Lemma (ensures (let st' = madd_to_store_split_raw st s k v s' d d2 in
                    pointed_to_inv_local st' s2))
          [SMTPat (pointed_to_inv_local (madd_to_store_split_raw st s k v s' d d2) s2)]
  =
  let msp = MSP st s k v s' d d2 in
  let st' = madd_to_store_split_raw st s k v s' d d2 in
  if empty_slot st' s2 || stored_key st' s2 = Root || add_method_of st' s2 <> Spec.MAdd then ()
  else
    if s2 = s then (
      assert(points_to_dir st' s' d s);
      ()
    )
    else if s2 = msp_desc_slot msp then (
      assert(points_to_dir st' s d2 s2);
      ()
    )
    else (
      assert(empty_slot st s2 = empty_slot st' s2);
      assert(stored_key st s2 = stored_key st' s2);
      assert(add_method_of st s2 = add_method_of st' s2);

      let (s2',d2) = pointed_to_inv_local_find st s2 in

      (* s2' is inuse in st, so it cannot be s *)
      assert(s2' <> s);

      (* otherwise s2 = s, a case we have ruled out in this else branch *)
      assert(s2' <> s' \/ d2 <> d);

      assert(points_to_some_slot st' s2' d2);
      assert(pointed_slot st' s2' d2 = s2);
      ()
    )

let madd_to_store_split_pointed_to_inv
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:empty_slot_id st)
  (k:key) (v:value_type_of k)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_some_slot st s' d})
  (d2:bin_tree_dir)
  : Lemma (ensures (let st' = madd_to_store_split_raw st s k v s' d d2 in
                    pointed_to_inv st'))
          [SMTPat (madd_to_store_split_raw st s k v s' d d2)] =
  ()

let madd_to_store_split_no_self_edges
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:empty_slot_id st)
  (k:key) (v:value_type_of k)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_some_slot st s' d})
  (d2:bin_tree_dir)
  : Lemma (ensures (let st' = madd_to_store_split_raw st s k v s' d d2 in
                    no_self_edge st'))
          [SMTPat (madd_to_store_split_raw st s k v s' d d2)] =
  let msp = MSP st s k v s' d d2 in
  let st' = madd_to_store_split_raw st s k v s' d d2 in
  assert(s <> s');
  let aux s2
    : Lemma (ensures (no_self_edge_local st' s2))
            [SMTPat (no_self_edge_local st' s2)] =
    if not (points_to st' s2 s2) then ()
    else
      let d2 = pointed_dir st' s2 s2 in
      if s2 = s then
        msp_desc_slot_not_added_slot msp
      else (
        assert(points_to_info st' s2 d2 = points_to_info st s2 d2);
        assert(no_self_edge_local st s2);
        ()
      )
  in
  ()

let madd_to_store_split
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:empty_slot_id st)
  (k:key) (v:value_type_of k)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_some_slot st s' d})
  (d2:bin_tree_dir)
  : Tot (st': vstore vcfg{let od = other_dir d in
                          let s2 = pointed_slot st s' d in
                          let od2 = other_dir d2 in

                          // st and st' identical except at s, s'
                          identical_except2 st st' s s' /\

                          // nothing changes in slot s', except it now points to s in direction d
                          inuse_slot st' s' /\
                          stored_key st' s' = stored_key st s' /\
                          stored_value st' s' = stored_value st s' /\
                          add_method_of st' s' = add_method_of st s' /\
                          points_to_dir st' s' d s /\
                          points_to_info st' s' od = points_to_info st s' od /\

                          // slot s contains (k, v, MAdd) and points to s2 along direction d2
                          inuse_slot st' s /\
                          stored_key st' s = k /\ stored_value st' s = v /\ add_method_of st' s = Spec.MAdd /\
                          points_to_none st' s od2 /\
                          points_to_dir st' s d2 s2})
  = madd_to_store_split_raw st s k v s' d d2

noeq type madd_root_param (vcfg: verifier_config) =
  | MSR: st: vstore vcfg ->
         s: empty_slot_id st ->
         v: value_type_of Root ->
         madd_root_param vcfg

let madd_to_store_root_raw #vcfg (msr: madd_root_param vcfg): vstore_raw vcfg =
  match msr with
  | MSR st s v ->
    let e = VStoreE Root v Spec.MAdd None None in
    update_slot st s e

let msr_store_pre #vcfg (msr: madd_root_param vcfg) =
  MSR?.st msr

let msr_store_post #vcfg msr =
  madd_to_store_root_raw #vcfg msr

let msr_slot #vcfg msr: slot_id vcfg =
  match msr with
  | MSR _ s _ -> s

let msr_value #vcfg (msr: madd_root_param vcfg): value_type_of Root =
  match msr with
  | MSR _ _ v -> v

let msr_edges_identical #vcfg (msr: madd_root_param vcfg) (e: sds vcfg):
  Lemma (ensures (is_edge (msr_store_pre msr) e =
                  is_edge (msr_store_post msr) e)) =
  let s1,d,s2 = e in
  if s1 = msr_slot msr then ()
  else ()

let msr_identical_except #vcfg msr:
  Lemma (ensures (identical_except (msr_store_pre msr) (msr_store_post msr) (msr_slot msr)))
        [SMTPat (madd_to_store_root_raw #vcfg msr)] =
  ()

let lemma_madd_to_store_root_points_inuse_local #vcfg msr:
  Lemma (ensures (points_to_inuse (msr_store_post msr)))
        [SMTPat (madd_to_store_root_raw #vcfg msr)] =

  let stn = msr_store_post msr in
  let stp = msr_store_pre msr in

  let aux s1 s2
    : Lemma (ensures (points_to_inuse_local stn s1 s2))
            [SMTPat (points_to_inuse_local stn s1 s2)] =
    assert(points_to_inuse_local stp s1 s2);
    if not (points_to stn s1 s2) then ()
    else
      let d12 = pointed_dir stn s1 s2 in

      (* since edges are identical, s1->s2 in an edge in store prev *)
      let e = s1,d12,s2 in
      msr_edges_identical msr e;
      assert(is_edge stp e);

      ()
  in
  ()

let lemma_madd_to_store_root_points_to_uniq #vcfg msr:
  Lemma (ensures (points_to_uniq (msr_store_post msr)))
        [SMTPat (madd_to_store_root_raw #vcfg msr)] =
  let stn = msr_store_post msr in
  let stp = msr_store_pre msr in

  let aux s1 s2 s3:
    Lemma (ensures (points_to_uniq_local stn s1 s2 s3))
          [SMTPat (points_to_uniq_local stn s1 s2 s3)] =
    if points_to_uniq_local stn s1 s2 s3 then ()
    else
      let e13 = s1, pointed_dir stn s1 s3, s3 in
      let e23 = s2, pointed_dir stn s2 s3, s3 in
      msr_edges_identical msr e13;
      msr_edges_identical msr e23;
      assert(points_to_uniq_local stp s1 s2 s3);
      ()
  in
  ()

let lemma_madd_to_store_root_pointed_to_inv #vcfg msr:
  Lemma (ensures (pointed_to_inv (msr_store_post msr)))
        [SMTPat (madd_to_store_root_raw #vcfg msr)] =
  let stn = msr_store_post msr in
  let stp = msr_store_pre msr in

  let aux s:
    Lemma (ensures (pointed_to_inv_local stn s))
          [SMTPat (pointed_to_inv_local stn s)] =
    if empty_slot stn s || stored_key stn s = Root || add_method_of stn s <> Spec.MAdd then ()
    else (
      assert(stored_key stn s <> Root);
      assert(stored_key stn (msr_slot msr) = Root);
      (* s is not the added slot since the added slot contains Root *)
      assert(s <> msr_slot msr);

      let s',d = pointed_to_inv_local_find stp s in
      let e = s',d,s in
      assert(is_edge stp e);
      msr_edges_identical msr e;
      assert(is_edge stn e);
      ()
    )
 in
 ()

let lemma_madd_to_store_root_no_self_edges #vcfg msr:
  Lemma (ensures (no_self_edge (msr_store_post msr)))
        [SMTPat (madd_to_store_root_raw #vcfg msr)] =
  let stn = msr_store_post msr in
  let stp = msr_store_pre msr in

  let aux s:
    Lemma (ensures (no_self_edge_local stn s))
          [SMTPat (no_self_edge_local stn s)] =
    if not (points_to stn s s) then ()
    else
      let e = s,pointed_dir stn s s,s in
      msr_edges_identical msr e;
      assert(is_edge stp e);
      assert(no_self_edge_local stp s);
      ()
  in
  ()

let madd_to_store_root
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:empty_slot_id st)
  (v:value_type_of Root)
  : Tot (st':vstore vcfg{// st and st' identical except at s, s'
                         identical_except st st' s /\

                         // slot s contains (Root, v, MAdd) and points to none
                         inuse_slot st' s /\
                         get_inuse_slot st' s = VStoreE Root v Spec.MAdd None None})
  = madd_to_store_root_raw (MSR st s v)

noeq type badd_param (vcfg: verifier_config)  =
  | BAS: st: vstore vcfg ->
         s: empty_slot_id st ->
         k: key ->
         v: value_type_of k -> badd_param vcfg

let apply_bas #vcfg (bas: badd_param vcfg) =
  match bas with
  | BAS st s k v ->
    let e = VStoreE k v Spec.BAdd None None in
    update_slot st s e

let bas_store_pre #vcfg (bas: badd_param vcfg) =
  BAS?.st bas

let bas_store_post #vcfg bas =
  apply_bas #vcfg bas

let bas_key #vcfg (bas: badd_param vcfg) =
  BAS?.k bas

let bas_value #vcfg (bas: badd_param vcfg) =
  BAS?.v bas

let bas_slot #vcfg (bas: badd_param vcfg) =
  BAS?.s bas

let bas_edges_identical #vcfg bas e
  : Lemma (ensures (is_edge (bas_store_pre #vcfg bas) e =
                    is_edge (bas_store_post bas) e)) =
  let s1,d,s2 = e in
  if s1 = bas_slot bas then ()
  else ()

let bas_identical_except #vcfg bas
  : Lemma (ensures (identical_except (bas_store_pre bas) (bas_store_post bas) (bas_slot bas)))
          [SMTPat (apply_bas #vcfg bas)] = ()

let lemma_bas_points_to_inuse #vcfg bas
  : Lemma (ensures (points_to_inuse (bas_store_post bas)))
          [SMTPat (apply_bas #vcfg bas)] =
  let stp = bas_store_pre bas in
  let stn = bas_store_post bas in

  let aux s1 s2
    : Lemma (ensures (points_to_inuse_local stn s1 s2))
            [SMTPat (points_to_inuse_local stn s1 s2)] =
    if not (points_to stn s1 s2) then ()
    else
      let d12 = pointed_dir stn s1 s2 in

      (* since edges are identical, s1->s2 in an edge in store prev *)
      let e = s1,d12,s2 in
      bas_edges_identical bas e;
      assert(is_edge stp e);

      ()
 in
 ()

let lemma_bas_points_to_uniq #vcfg bas:
  Lemma (ensures (points_to_uniq (bas_store_post bas)))
        [SMTPat (apply_bas #vcfg bas)] =
  let stn = bas_store_post bas in
  let stp = bas_store_pre bas in

  let aux s1 s2 s3:
    Lemma (ensures (points_to_uniq_local stn s1 s2 s3))
          [SMTPat (points_to_uniq_local stn s1 s2 s3)] =
    if points_to_uniq_local stn s1 s2 s3 then ()
    else
      let e13 = s1, pointed_dir stn s1 s3, s3 in
      let e23 = s2, pointed_dir stn s2 s3, s3 in
      bas_edges_identical bas e13;
      bas_edges_identical bas e23;
      assert(points_to_uniq_local stp s1 s2 s3);
      ()
  in
  ()

let lemma_bas_pointed_to_inv #vcfg bas:
  Lemma (ensures (pointed_to_inv (bas_store_post bas)))
        [SMTPat (apply_bas #vcfg bas)] =
  let stn = bas_store_post bas in
  let stp = bas_store_pre bas in

  let aux s:
    Lemma (ensures (pointed_to_inv_local stn s))
          [SMTPat (pointed_to_inv_local stn s)] =
    if empty_slot stn s || stored_key stn s = Root || add_method_of stn s <> Spec.MAdd then ()
    else (
      (* s is not the added slot since the added slot contains Root *)
      assert(s <> bas_slot bas);

      let s',d = pointed_to_inv_local_find stp s in
      let e = s',d,s in
      assert(is_edge stp e);
      bas_edges_identical bas e;
      assert(is_edge stn e);
      ()
    )
 in
 ()

let lemma_bas_no_self_edges #vcfg bas:
  Lemma (ensures (no_self_edge (bas_store_post bas)))
        [SMTPat (apply_bas #vcfg bas)] =
  let stn = bas_store_post bas in
  let stp = bas_store_pre bas in

  let aux s:
    Lemma (ensures (no_self_edge_local stn s))
          [SMTPat (no_self_edge_local stn s)] =
    if not (points_to stn s s) then ()
    else
      let e = s,pointed_dir stn s s,s in
      bas_edges_identical bas e;
      assert(is_edge stp e);
      assert(no_self_edge_local stp s);
      ()
  in
  ()

let badd_to_store
      (#vcfg:verifier_config)
      (st:vstore vcfg)
      (s:empty_slot_id st)
      (k:key)
      (v:value_type_of k)
  : Tot (st':vstore vcfg {// st and st' identical except for s
                          identical_except st st' s /\
                          inuse_slot st' s /\
                          get_inuse_slot st' s = VStoreE k v Spec.BAdd None None})
  =
  let bas = BAS st s k v in
  apply_bas bas

noeq type mevict_param (vcfg: verifier_config) =
  | MEV: st:vstore vcfg ->
         s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right} ->
         s':inuse_slot_id st ->
         d:bin_tree_dir{points_to_some_slot st s' d ==> points_to_dir st s' d s} ->
         mevict_param vcfg

let apply_mev #vcfg (mev: mevict_param vcfg) =
  match mev with
  | MEV st s s' d ->
    let VStoreE k' v' am' ld' rd' = get_inuse_slot st s' in
    let e' = if d = Left
             then VStoreE k' v' am' None rd'
             else VStoreE k' v' am' ld' None in
    let st = update_slot st s' e' in
    Seq.upd st s None

let mev_store_pre #vcfg (mev: mevict_param vcfg) =
  MEV?.st mev

let mev_store_post #vcfg mev =
  apply_mev #vcfg mev

let mev_slot #vcfg (mev: mevict_param vcfg) =
  MEV?.s mev

let mev_anc_slot #vcfg (mev: mevict_param vcfg) =
  MEV?.s' mev

let mev_dir #vcfg (mev: mevict_param vcfg) =
  MEV?.d mev

let mev_deletes_edge #vcfg mev =
  points_to_some_slot (mev_store_pre mev) (mev_anc_slot mev) (mev_dir #vcfg mev)

let mev_deleted_edge #vcfg (mev: mevict_param vcfg {mev_deletes_edge mev}): sds vcfg =
  (mev_anc_slot mev), (mev_dir mev), (mev_slot mev)

let mev_deleted_edge_in_pre_not_in_post #vcfg (mev: mevict_param vcfg {mev_deletes_edge mev})
  : Lemma (ensures (let e = mev_deleted_edge mev in
                    is_edge (mev_store_pre mev) e /\
                    is_nonedge (mev_store_post mev) e))
          [SMTPat (apply_mev mev)] = ()

let mev_edge_in_post_in_pre #vcfg mev e
  : Lemma (ensures (is_edge (mev_store_post #vcfg mev) e ==>
                    is_edge (mev_store_pre mev) e)) = ()

let mev_edge_in_pre_in_post #vcfg mev e
  : Lemma (requires (is_edge (mev_store_pre #vcfg mev) e /\
                     (mev_deletes_edge mev ==> e <> mev_deleted_edge mev)))
          (ensures (is_edge (mev_store_post mev) e)) =
  let s1,d2,s2 = e in
  if s1 = mev_anc_slot mev then (
    assert(d2 <> mev_dir mev);
    ()
  )
  else (
    assert(s1 <> mev_slot mev);
    ()
  )

let mev_del_slot_empty #vcfg mev
  : Lemma (ensures (empty_slot (mev_store_post mev) (mev_slot mev)))
          [SMTPat (apply_mev #vcfg mev)]  = ()

let lemma_mev_points_to_inuse #vcfg mev
  : Lemma (ensures (points_to_inuse (mev_store_post mev)))
          [SMTPat (apply_mev #vcfg mev)] =
  let stp = mev_store_pre mev in
  let stn = mev_store_post mev in

  let aux s1 s2
    : Lemma (ensures (points_to_inuse_local stn s1 s2))
            [SMTPat (points_to_inuse_local stn s1 s2)] =
    if not (points_to stn s1 s2) then ()
    else (
      let d12 = pointed_dir stn s1 s2 in
      let e = s1,d12,s2 in

      (* every edge in post is an edge in pre *)
      mev_edge_in_post_in_pre mev e;
      assert(is_edge stp e);
      assert(points_to_inuse_local stp s1 s2);

      assert(s1 <> mev_slot mev);
      if s1 = mev_anc_slot mev then admit()
      else (

        assert(get_slot stp s1 = get_slot stn s1);
        if s2 = mev_slot mev then (
          assert(points_to stp s1 s2);
          //assert(points_to stp (mev_anc_slot mev) s2);
          admit()
        )
        else

        admit()
      )
    )
  in
  ()

let mevict_from_store
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right})
  (s':inuse_slot_id st)
  (d:bin_tree_dir{points_to_some_slot st s' d ==> points_to_dir st s' d s})
  : Tot (st':vstore vcfg {let od = other_dir d in

                          // st and st' identical except at s, s'
                          identical_except2 st st' s s' /\

                          // slot s is empty after update
                          empty_slot st' s /\

                          // nothing changes in slot s', except it points to none in directoin d
                          inuse_slot st' s' /\
                          stored_key st' s' = stored_key st s' /\
                          stored_value st' s' = stored_value st s' /\
                          add_method_of st' s' = add_method_of st s' /\
                          points_to_info st' s' od = points_to_info st s' od /\
                          points_to_none st' s' d
                          })
  = admit()

(*
noeq type bevict_param (vcfg: verifier_config) =
  | BEV: st: vstore vcfg ->
         s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right} ->
*)

let bevict_from_store
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right /\ add_method_of st s = Spec.BAdd})
  : Tot (st':vstore vcfg {// st and st' are identical except at slot s
                          identical_except st st' s /\

                          // slot s is empty after the update
                          empty_slot st' s})
  = admit()

let pointing_slot (#vcfg:_)
                (st:vstore vcfg)
                (s:inuse_slot_id st{Root <> stored_key st s /\ add_method_of st s = Spec.MAdd})
 : Tot (s':inuse_slot_id st{points_to st s' s}) = admit()

let as_map (#vcfg:_) (st:ismap_vstore vcfg) : Spec.vstore = admit()

let lemma_ismap_update_value
      (#vcfg:_)
      (st:ismap_vstore vcfg)
      (s:inuse_slot_id st)
      (v:value_type_of (stored_key st s))
  : Lemma (ensures (is_map (update_value st s v)))
  = admit()

let lemma_ismap_madd_to_store (#vcfg:_) (st:ismap_vstore vcfg)
  (s:empty_slot_id st)
  (k:key) (v:value_type_of k)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_none st s' d})
  : Lemma (requires (not (store_contains_key st k)))
          (ensures (is_map (madd_to_store st s k v s' d)))
  = admit()

let lemma_ismap_madd_to_store_split
  (#vcfg: verifier_config)
  (st:ismap_vstore vcfg)
  (s:empty_slot_id st)
  (k:key) (v:value_type_of k)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_some_slot st s' d})
  (d2:bin_tree_dir)
  : Lemma (requires (not (store_contains_key st k)))
          (ensures (is_map (madd_to_store_split st s k v s' d d2)))
  = admit()

let lemma_ismap_correct (#vcfg:_) (st:ismap_vstore vcfg) (s1 s2: inuse_slot_id st)
  : Lemma (requires (stored_key st s1 = stored_key st s2))
          (ensures (s1 = s2))
  = admit()

let lemma_empty_store_is_map (#vcfg:_):
  Lemma (ensures (is_map (empty_store vcfg))) = admit()

let lemma_empty_contains_nokey (#vcfg:_) (k:key):
  Lemma (ensures (let st = empty_store vcfg in
                  not (store_contains_key st k))) = admit()

let lemma_madd_root_to_store_is_map
      (#vcfg:_)
      (st:ismap_vstore vcfg{not (store_contains_key st Root)})
      (s:empty_slot_id st)
      (v:value_type_of Root)
  : Lemma (ensures (is_map (madd_to_store_root st s v))) = admit()

let lemma_as_map_empty (vcfg:_)
  : Lemma (ensures (let st = empty_store vcfg in
                     forall (k:key). as_map st k = None)) = admit()

let lemma_as_map_slot_key_equiv (#vcfg:_) (st:ismap_vstore vcfg) (s:inuse_slot_id _)
  : Lemma (ensures (let k = stored_key st s in
                    let stk = as_map st in
                    Spec.store_contains stk k /\
                    stored_value st s = Spec.stored_value stk k /\
                    add_method_of st s = Spec.add_method_of stk k)) = admit()

let slot_of_key (#vcfg:_) (st:ismap_vstore vcfg) (k: key{let stk = as_map st in
                                                                  Spec.store_contains stk k})
  : Tot (s: inuse_slot_id st {let stk = as_map st in
                              k = stored_key st s /\
                              stored_value st s = Spec.stored_value stk k /\
                              add_method_of st s = Spec.add_method_of stk k}) = admit()

let lemma_not_contains_after_mevict
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right})
  (s':inuse_slot_id st)
  (d:bin_tree_dir{points_to_some_slot st s' d ==> points_to_dir st s' d s}):
  Lemma (ensures (let st' = mevict_from_store st s s' d in
                  let k = stored_key st s in
                  is_map st' /\
                  not (store_contains_key st' k))) = admit()

let lemma_not_contains_after_bevict
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right /\ add_method_of st s = Spec.BAdd})
  : Lemma (ensures (let st' = bevict_from_store st s in
                    let k = stored_key st s in
                    is_map st' /\
                    not (store_contains_key st' k))) = admit()


(*
(* update the data value of a data key *)
let update_data_value
  (st:vstore)
  (s:data_slot_id st)
  (v:value{DVal? v})
  : Tot (st':vstore {Seq.length st = Seq.length st' /\
                     inuse_slot st' s /\
                     stored_value st' s = v}) =
  assert(not (desc_in_store st s Left));
  assert(not (desc_in_store st s Right));
  let Some (VStoreE k _ am _ _) = get_slot st s in
  let st' = update_slot st s (VStoreE k v am None None) in
  assert(Seq.length st = Seq.length st');
  assert(inuse_slot st' s);
  assert(stored_value st' s = v);

  let aux1 (s0:slot_id st'):
    Lemma (ensures (inuse_slot st' s0 = inuse_slot st s0 /\
                    (inuse_slot st' s0 ==>
                     stored_key st' s0 = stored_key st s0))) = ()
  in

  let aux (s0:slot_id st'):
    Lemma (ensures (store_inv_slot st' s0))
          [SMTPat (store_inv_slot st' s0)] =
    if s0 = s then ()
    else (
      assert(Seq.index st s0 = Seq.index st' s0);
      if empty_slot st s0 then ()
      else if is_data_key (stored_key st s0) then ()
      else
        admit()
    )
    in
  assert(store_inv_local st');
  st'


let lemma_lookup_key_returns_k (st:vstore) (k:key)
  : Lemma (requires (store_contains_key st k))
          (ensures (VStoreE?.k (Some?.v (lookup_key st k)) = k))
  = lemma_filter_correct1 (has_key k) st 0

let lemma_lookup_key_returns_None (st:vstore) (k:key)
  : Lemma (requires (lookup_key st k = None))
          (ensures (forall i. not (has_key k (Seq.index st i))))
  = if Seq.length (filter (has_key k) st) = 0
    then lemma_filter_all_not (has_key k) st
    else lemma_filter_correct1 (has_key k) st 0

let lemma_store_contains_key (st:vstore) (k:key)
  : Lemma (requires (exists s. stored_key st s = k))
          (ensures (store_contains_key st k))
  = lemma_filter_exists (has_key k) st;
    lemma_filter_correct1 (has_key k) st 0

let lemma_has_key (st:vstore) (s:slot_id) (k:key)
  : Lemma (requires (has_key k (get_slot st s)))
          (ensures (store_contains st s /\ stored_key st s = k))
  = ()

let lemma_store_contains_key_inv (st:vstore) (k:key)
  : Lemma (requires (store_contains_key st k))
          (ensures (exists s. stored_key st s = k))
  = let s' = filter (has_key k) st in
    if Seq.length s' > 0
    then
      let i = filter_index_map (has_key k) st 0 in
      lemma_has_key st i k

let stored_value_by_key (st:vstore) (k:key{store_contains_key st k})
  : value_type_of k
  = lemma_lookup_key_returns_k st k;
    VStoreE?.v (Some?.v (lookup_key st k))

let add_method_of_by_key (st:vstore) (k:key{store_contains_key st k})
  : add_method
  = VStoreE?.am (Some?.v (lookup_key st k))

(* Two cases where it's safe to add an entry (e) to the store (st) at slot s:
   * e.k is not in st and s is empty
   * e.k is already at s *)
let compatible_entry (st:vstore) (s:st_index st) (e:vstore_entry)
  = (not (store_contains st s) /\ not (store_contains_key st e.k)) \/
    (store_contains st s /\ stored_key st s = e.k)

let lemma_update_slot_compatible_entry_is_map
      (st:vstore{is_map st})
      (s:st_index st)
      (e:vstore_entry{compatible_entry st s e})
  : Lemma (is_map (update_slot st s e))
          [SMTPat (is_map (update_slot st s e))]
  = let st_upd = update_slot st s e in
    let aux (s0:slot_id{store_contains st_upd s0})
            (s0':slot_id{store_contains st_upd s0' /\ s0' <> s0})
          : Lemma (stored_key st_upd s0 <> stored_key st_upd s0')
                  [SMTPat (Seq.index st_upd s0); SMTPat (Seq.index st_upd s0')]
          = if s0 = s
            then assert (stored_key st s0' <> e.k)
            else if s0' = s
            then assert (stored_key st s0 <> e.k) in
    assert (is_map st_upd)

let lemma_add_to_store_is_map1
      (st:vstore)
      (s:st_index st{not (store_contains st s)})
      (k:key{not (store_contains_key st k)})
      (v:value_type_of k)
      (am:add_method)
  : Lemma (requires (is_map st))
          (ensures (is_map (add_to_store st s k v am)))
  = () // proved by lemma_update_compatible_entry_is_map

let lemma_add_to_store_is_map2
      (st:vstore)
      (s:st_index st{not (store_contains st s)})
      (k:key{store_contains_key st k})
      (v:value_type_of k)
      (am:add_method)
  : Lemma (ensures (~ (is_map (add_to_store st s k v am))))
  = let st_upd = add_to_store st s k v am in
    assert (stored_key st_upd s = k);
    lemma_store_contains_key_inv st k;
    Classical.exists_elim
      (exists (s':slot_id{store_contains st_upd s' /\ s' <> s}).
      stored_key st_upd s' = stored_key st_upd s)
      (Squash.get_proof (exists s. stored_key st s = k))
      (fun s' -> assert (stored_key st_upd s' = k));
    // we have shown two different slots with the same key, so the invariant is violated
    ()

let lemma_lookup_key_update_value
      (st:vstore)
      (s:slot_id{store_contains st s})
      (v:value_type_of (stored_key st s))
      (k:key)
  : Lemma (let res = lookup_key st k in
           let res' = lookup_key (update_value st s v) k in
           (None? res /\ None? res') \/
           (Some? res /\ Some? res' /\ VStoreE?.am (Some?.v res) = VStoreE?.am (Some?.v res')))
  = let stf = filter (has_key k) st in
    let Some (VStoreE ks _ am l r) = Seq.index st s in
    assert (Seq.length stf = Seq.length (filter (has_key k) (update_value st s v)));
    if Seq.length stf > 0
    then (
      if filter_index_map (has_key k) st 0 = s
      then lemma_filter_update_index_eq (has_key k) st s (Some (VStoreE ks v am l r))
      else lemma_filter_update_index_neq (has_key k) st s (Some (VStoreE ks v am l r)) 0
    )

let lemma_update_value_preserves_keys
      (st:vstore)
      (s:slot_id{store_contains st s})
      (v:value_type_of (stored_key st s))
      (k:key)
  : Lemma (store_contains_key st k = store_contains_key (update_value st s v) k)
  = lemma_lookup_key_update_value st s v k

let lemma_update_value_preserves_key_with_MAdd
  (st:vstore)
  (s:slot_id{store_contains st s})
  (v:value_type_of (stored_key st s))
  (k:key)
  : Lemma (ensures store_contains_key_with_MAdd st k =
                     store_contains_key_with_MAdd (update_value st s v) k)
  = lemma_lookup_key_update_value st s v k

let lemma_add_different_key_to_store_preserves_keys_with_MAdd
  (st:vstore)
  (s:st_index st{not (store_contains st s)})
  (k:key)
  (v:value_type_of k)
  (k0:key)
  : Lemma (requires k <> k0)
          (ensures store_contains_key_with_MAdd st k0 =
                     store_contains_key_with_MAdd (add_to_store st s k v Spec.MAdd) k0)
  = let stf = filter (has_key k0) st in
    if Seq.length stf > 0
    then (
      assert (filter_index_map (has_key k0) st 0 <> s);
      lemma_filter_update_index_neq (has_key k0) st s (Some (VStoreE k v Spec.MAdd false false)) 0
    )

let lemma_add_to_store_BAdd_preserves_key_with_MAdd
  (st:vstore)
  (s:st_index st{not (store_contains st s)})
  (k:key{not (store_contains_key st k)})
  (v:value_type_of k)
  (k0:key)
  : Lemma (ensures store_contains_key_with_MAdd st k0 =
                     store_contains_key_with_MAdd (add_to_store st s k v Spec.BAdd) k0)
  = let stf = filter (has_key k0) st in
    if Seq.length stf = 0
    then (
      let st_upd = add_to_store st s k v Spec.BAdd in
      if k = k0
      then (
        assert (has_key k0 (Seq.index st_upd s));
        lemma_filter_all_not (has_key k0) st;
        assert (forall j. j <> s ==> not (has_key k0 (Seq.index st_upd j)));
        lemma_filter_unique (has_key k0) st_upd s
      )
    )
    else (
      lemma_filter_correct1 (has_key k0) st 0;
      assert (k <> k0);
      assert (filter_index_map (has_key k0) st 0 <> s);
      lemma_filter_update_index_neq (has_key k0) st s (Some (VStoreE k v Spec.BAdd false false)) 0
    )

let lemma_add_to_store_MAdd_adds_key_with_MAdd
  (st:vstore)
  (s:st_index st{not (store_contains st s)})
  (k:key{not (store_contains_key st k)})
  (v:value_type_of k)
  : Lemma (ensures store_contains_key_with_MAdd (add_to_store st s k v Spec.MAdd) k)
  = let st_upd = add_to_store st s k v Spec.MAdd in
    assert (has_key k (Seq.index st_upd s));
    lemma_lookup_key_returns_None st k;
    lemma_filter_all_not (has_key k) st;
    assert (forall j. j <> s ==> not (has_key k (Seq.index st_upd j)));
    lemma_filter_unique (has_key k) st_upd s

let lemma_lookup_key_update_in_store
      (st:vstore)
      (s:slot_id{store_contains st s})
      (d:bin_tree_dir)
      (b:bool)
      (k:key)
  : Lemma (let res = lookup_key st k in
           let res' = lookup_key (update_in_store st s d b) k in
           (None? res /\ None? res') \/
           (Some? res /\ Some? res' /\ VStoreE?.am (Some?.v res) = VStoreE?.am (Some?.v res')))
  = let stf = filter (has_key k) st in
    let Some (VStoreE ks v am l r) = Seq.index st s in
    let newelem = match d with
                  | Left -> Some (VStoreE ks v am b r)
                  | Right -> Some (VStoreE ks v am l b) in
    assert (Seq.length stf = Seq.length (filter (has_key k) (update_in_store st s d b)));
    if Seq.length stf > 0
    then (
      (** TODO: For some reason this started failing with the updated vevictb/vevictbm *)
      (*
      if filter_index_map (has_key k) st 0 = s
      then lemma_filter_update_index_eq (has_key k) st s newelem
      else lemma_filter_update_index_neq (has_key k) st s newelem 0
      *)
      admit()
    )

let lemma_update_in_store_preserves_keys
  (st:vstore)
  (s:st_index st{store_contains st s})
  (d:bin_tree_dir)
  (b:bool)
  (k:key)
  : Lemma (ensures store_contains_key st k = store_contains_key (update_in_store st s d b) k)
  = lemma_lookup_key_update_in_store st s d b k

let lemma_update_in_store_preserves_key_with_MAdd
  (st:vstore)
  (s:st_index st{store_contains st s})
  (d:bin_tree_dir)
  (b:bool)
  (k:key)
  : Lemma (ensures store_contains_key_with_MAdd st k =
                     store_contains_key_with_MAdd (update_in_store st s d b) k)
  = lemma_lookup_key_update_in_store st s d b k

let lemma_evict_from_store_evicts_key
  (st:vstore)
  (s:st_index st{store_contains st s})
  : Lemma (requires is_map st)
          (ensures not (store_contains_key (evict_from_store st s) (stored_key st s)))
  = let k = stored_key st s in
    let st_upd = evict_from_store st s in
    let res = filter (has_key k) st_upd in
    lemma_filter_all_not_inv (has_key k) st_upd;
    assert (Seq.length res = 0)

let lemma_lookup_key_evict_from_store
      (st:vstore)
      (s:slot_id{store_contains st s})
      (k:key{k <> stored_key st s})
  : Lemma (lookup_key st k = lookup_key (evict_from_store st s) k)
  = let stf = filter (has_key k) st in
    if Seq.length stf > 0
    then (
      assert (filter_index_map (has_key k) st 0 <> s);
      lemma_filter_update_index_neq (has_key k) st s None 0
    )

let lemma_evict_from_store_preserves_key_with_MAdd
  (st:vstore)
  (s:st_index st{store_contains st s})
  (k:key)
  : Lemma (requires (k <> stored_key st s))
          (ensures (store_contains_key_with_MAdd st k = store_contains_key_with_MAdd (evict_from_store st s) k))
  = lemma_lookup_key_evict_from_store st s k

let lemma_get_slot_lookup_key (st:vstore{is_map st}) (s:slot_id) (k:key)
  : Lemma (requires (store_contains st s /\ stored_key st s = k))
          (ensures (get_slot st s = lookup_key st k))
  = let s' = filter (has_key k) st in
    lemma_filter_unique (has_key k) st s

let lemma_evict_from_store_BAdd_preserves_key_with_MAdd
  (st:vstore{is_map st})
  (s:slot_id{store_contains st s})
  (k:key)
  : Lemma (requires (add_method_of st s = Spec.BAdd))
          (ensures (store_contains_key_with_MAdd st k =
                      store_contains_key_with_MAdd (evict_from_store st s) k))
  = if k = stored_key st s
    then lemma_get_slot_lookup_key st s k
    else lemma_lookup_key_evict_from_store st s k

let lemma_slot_key_equiv_update_value
      (st:vstore)
      (s:slot_id)
      (s':slot_id{store_contains st s'})
      (k:key)
      (v:value_type_of (stored_key st s'))
  : Lemma (requires (slot_key_equiv st s k /\ s <> s'))
          (ensures (slot_key_equiv (update_value st s' v) s k))
  = ()

let rec as_map_aux (l:vstore)
  : Tot Spec.vstore (decreases (Seq.length l)) =
  let n = Seq.length l in
  if n = 0 then Spec.empty_store
  else
    let l' = prefix l (n - 1) in
    let f' = as_map_aux l' in
    match Seq.index l (n - 1) with
    | None -> f'
    | Some (VStoreE k v a _ _) ->
      Spec.add_to_store f' k v a

let as_map (st:vstore{is_map st}) : Spec.vstore =
  as_map_aux st

let rec lemma_as_map_empty (n:nat)
  : Lemma (ensures (let st = empty_store n in
                     forall (k:key). as_map st k = None))
          (decreases n)
  = if n <> 0
    then (
      lemma_prefix_create n (None #vstore_entry) (n-1);
      lemma_as_map_empty (n-1)
    )

let lemma_is_map_prefix (l:vstore) (i:seq_index l)
  : Lemma (requires (is_map l))
          (ensures (is_map (prefix l i)))
          [SMTPat (is_map (prefix l i))]
  = ()

let rec lemma_as_map_slot_key_equiv_aux
      (l:vstore)
      (s:slot_id)
      (k:key)
      (v:value_type_of k)
      (am:add_method)
      (lb rb:bool)
  : Lemma (requires (s < Seq.length l /\
                     Seq.index l s = Some (VStoreE k v am lb rb) /\
                     is_map l))
          (ensures (Spec.store_contains (as_map_aux l) k /\
                    Spec.stored_value (as_map_aux l) k = v /\
                    Spec.add_method_of (as_map_aux l) k = am))
          (decreases (Seq.length l))
  = let n = Seq.length l in
    if n <> 0
    then
      let l' = prefix l (n - 1) in
      match Seq.index l (n - 1) with
      | None -> lemma_as_map_slot_key_equiv_aux l' s k v am lb rb
      | Some (VStoreE k2 v2 am2 _ _) ->
          if s < n - 1
          then lemma_as_map_slot_key_equiv_aux l' s k v am lb rb

let lemma_as_map_slot_key_equiv (st:vstore{is_map st}) (s:slot_id) (k:key)
  : Lemma (requires (slot_key_equiv st s k))
          (ensures (Spec.store_contains (as_map st) k /\
                    stored_value st s = Spec.stored_value (as_map st) k /\
                    add_method_of st s = Spec.add_method_of (as_map st) k))
  = let Some (VStoreE k v a l r) = get_slot st s in
    lemma_as_map_slot_key_equiv_aux st s k v a l r

let rec lemma_as_map_aux_does_not_contain_key
      (l:vstore)
      (k:key)
  : Lemma (requires (forall i. not (has_key k (Seq.index l i))))
          (ensures (not (Spec.store_contains (as_map_aux l) k)))
          (decreases (Seq.length l))
  = let n = Seq.length l in
    if n <> 0
    then
      let l' = prefix l (n - 1) in
      lemma_as_map_aux_does_not_contain_key l' k

let lemma_store_rel_contains_key (st:vstore) (st':Spec.vstore) (k:key)
  : Lemma (requires (store_rel st st'))
          (ensures (store_contains_key st k = Spec.store_contains st' k))
  = if store_contains_key st k
    then (
      lemma_store_contains_key_inv st k;
      Classical.exists_elim
        (Spec.store_contains (as_map st) k)
        (Squash.get_proof (exists s. slot_key_equiv st s k))
        (fun s -> lemma_as_map_slot_key_equiv st s k)
    )
    else (
      lemma_lookup_key_returns_None st k;
      lemma_as_map_aux_does_not_contain_key st k
    )

let lemma_store_rel_stored_value (st:vstore) (st':Spec.vstore) (k:key)
  : Lemma (requires (store_rel st st' /\ store_contains_key st k))
          (ensures (stored_value_by_key st k = Spec.stored_value st' k))
  = lemma_store_contains_key_inv st k;
    Classical.exists_elim
      (stored_value_by_key st k = Spec.stored_value (as_map st) k)
      (Squash.get_proof (exists s. slot_key_equiv st s k))
      (fun s -> lemma_get_slot_lookup_key st s k;
             lemma_as_map_slot_key_equiv st s k)

let lemma_store_rel_add_method_of (st:vstore) (st':Spec.vstore) (k:key)
  : Lemma (requires (store_rel st st' /\ store_contains_key st k))
          (ensures (add_method_of_by_key st k = Spec.add_method_of st' k))
  = lemma_store_contains_key_inv st k;
    Classical.exists_elim
      (add_method_of_by_key st k = Spec.add_method_of (as_map st) k)
      (Squash.get_proof (exists s. slot_key_equiv st s k))
      (fun s -> lemma_get_slot_lookup_key st s k;
             lemma_as_map_slot_key_equiv st s k)

let compatible_entry_prefix (st:vstore) (s:st_index st) (e:vstore_entry) (i:st_index st)
  : Lemma (requires (compatible_entry st s e /\ s < i))
          (ensures (compatible_entry (prefix st i) s e))
          [SMTPat (compatible_entry (prefix st i) s e)]
  = if not (store_contains st s)
    then (
      lemma_lookup_key_returns_None st e.k;
      lemma_filter_all_not_inv (has_key e.k) (prefix st i)
    )

#push-options "--fuel 1,1 --ifuel 2,2"
let rec lemma_as_map_update (st:vstore{is_map st})
                            (s:st_index st)
                            (e:vstore_entry{compatible_entry st s e})
  : Lemma (ensures (let m = as_map st in
                    let m' = as_map (update_slot st s e) in
                    m' e.k = Some (Spec.VStore e.v e.am) /\
                    (forall k. k <> e.k ==> m' k = m k)))
          (decreases (Seq.length st))
  = let n = Seq.length st in
    if n <> 0
    then
      let st_upd = update_slot st s e in
      let st_p = prefix st (n - 1) in
      let st_upd_p = prefix st_upd (n - 1) in
      if s < n - 1
      then (
        let st_p_upd = update_slot st_p s e in
        lemma_as_map_update st_p s e;
        assert (Seq.equal st_p_upd st_upd_p)
      )
      else ( // s = n - 1
        assert (Seq.equal st_p st_upd_p)
      )
#pop-options

let lemma_store_rel_update_value (st:vstore) (st':Spec.vstore) (s:slot_id) (k:key) (v:value_type_of k)
  : Lemma (requires (store_rel st st' /\ slot_key_equiv st s k))
          (ensures (store_rel (update_value st s v) (Spec.update_store st' k v)))
  = let Some (VStoreE _ _ am l r) = get_slot st s in
    lemma_as_map_update st s (VStoreE k v am l r)

let lemma_store_rel_update_in_store (st:vstore) (st':Spec.vstore) (s:slot_id) (d:bin_tree_dir) (b:bool)
  : Lemma (requires (store_rel st st' /\ store_contains st s))
          (ensures (store_rel (update_in_store st s d b) st'))
  = let Some (VStoreE k v am l r) = get_slot st s in
    assert (slot_key_equiv st s k); // assert needed to trigger pattern
    let e = match d with
            | Left -> VStoreE k v am b r
            | Right -> VStoreE k v am l b in
    lemma_as_map_update st s e

let lemma_store_rel_add_to_store (st:vstore) (st':Spec.vstore) (s:st_index st) (k:key) (v:value_type_of k) (am:add_method)
  : Lemma (requires (store_rel st st' /\ not (store_contains st s) /\ not (Spec.store_contains st' k)))
          (ensures (store_rel (add_to_store st s k v am) (Spec.add_to_store st' k v am)))
  = lemma_as_map_update st s (VStoreE k v am false false)

let rec lemma_as_map_evict (st:vstore{is_map st}) (s:st_index st) (k:key)
  : Lemma (requires (slot_key_equiv st s k))
          (ensures (let m = as_map st in
                    let m' = as_map (evict_from_store st s) in
                    m' k = None /\ (forall k'. k' <> k ==> m' k' = m k')))
          (decreases (Seq.length st))
  = let n = Seq.length st in
    if n <> 0
    then
      let stupd = evict_from_store st s in
      let stp = prefix st (n - 1) in
      let stupdp = prefix stupd (n - 1) in
      if s < n - 1
      then (
        lemma_as_map_evict stp s k;
        assert (Seq.equal stupdp (evict_from_store stp s))
      )
      else (  // s = n - 1
        assert (Seq.equal stp stupdp);
        lemma_as_map_aux_does_not_contain_key stp k
      )

let lemma_store_rel_evict_from_store (st:vstore) (st':Spec.vstore) (s:st_index st) (k:key)
  : Lemma (requires (store_rel st st' /\ slot_key_equiv st s k))
          (ensures (store_rel (evict_from_store st s) (Spec.evict_from_store st' k)))
  = lemma_as_map_evict st s k
*)
