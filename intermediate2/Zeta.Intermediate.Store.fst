module Zeta.Intermediate.Store

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
         v: value vcfg.app {compatible (stored_key st s) v} -> update_val_param vcfg

let uvp_slot #vcfg (uvp: update_val_param vcfg): slot_id vcfg =
  UVP?.s uvp

let uvp_val #vcfg (uvp: update_val_param vcfg) =
  UVP?.v uvp

let apply_update_val #vcfg (uvp: update_val_param vcfg) =
  match uvp with
  | UVP st s v ->
    let VStoreE (k,v') am lp rp p = get_inuse_slot st s in
    let e' = VStoreE (k,v) am lp rp p in
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

(* update a value of a key *)
let update_value
  (#vcfg:_)
  (st:vstore vcfg)
  (s:inuse_slot_id st)
  (v:value vcfg.app {compatible (stored_key st s) v})
  : Tot (st':vstore vcfg {identical_except st st' s /\
                          inuse_slot st' s /\
                          (let VStoreE (k1,_) am1 ld1 rd1 p1 = get_inuse_slot st s in
                           let VStoreE (k2,v2) am2 ld2 rd2 p2 = get_inuse_slot st' s in
                           k1 = k2 /\ am1 = am2 /\ ld1 = ld2 /\ rd1 = rd2 /\ p1 = p2 /\ v2 = v)})
  = let uvp = UVP st s v in
    apply_update_val uvp

noeq type madd_param (vcfg: verifier_config) =
  | MAP:   st: vstore vcfg ->
           s:empty_slot_id st ->
           r:record vcfg.app ->
           s':merkle_slot_id st ->
           d:bin_tree_dir {points_to_none st s' d} -> madd_param vcfg

let map_slot #vcfg (map: madd_param vcfg) =
  MAP?.s map

let map_record #vcfg (map: madd_param vcfg) =
  MAP?.r map

let map_dir #vcfg (map: madd_param vcfg) =
  MAP?.d map

let map_anc_slot #vcfg (map: madd_param vcfg) =
  MAP?.s' map

let apply_map #vcfg (map: madd_param vcfg) =
  match map with
  | MAP st s r s' d ->
    let p = (map_anc_slot map), (map_dir map) in
    let e = VStoreE r Spec.MAdd None None (Some p) in
    let st = update_slot st s e in
    let VStoreE r' am' ld' rd' p' = get_inuse_slot st s' in
    assert(None == (if d = Left then ld' else rd'));

    if d = Left then
      update_slot st s' (VStoreE r' am' (Some s) rd' p')
    else
      update_slot st s' (VStoreE r' am' ld' (Some s) p')

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
  (r:record vcfg.app)
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
                         get_inuse_slot st' s = VStoreE r Spec.MAdd None None (Some (s',d))
                         })
  = let map = MAP st s r s' d in
    apply_map map

noeq type madd_split_param (vcfg: verifier_config) =
  | MSP: st: vstore vcfg ->
         s: empty_slot_id st ->
         r: record vcfg.app ->
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
  | MSP _ _ r _ d d2 ->
    let st = msp_store_pre msp in
    let s =  msp_slot msp in
    let s' =  msp_anc_slot msp in
    let s2 = msp_desc_slot msp in
    let VStoreE kv' am' l' r' p' = get_inuse_slot st s' in
    let p = s',d in
    let e = (if d2 = Left then
               VStoreE r Spec.MAdd (Some s2) None (Some p)
             else
               VStoreE r Spec.MAdd None (Some s2) (Some p)) in

    let e' = (if d = Left then
                VStoreE kv' am' (Some s) r' p'
              else
                VStoreE kv' am' l' (Some s) p') in
    let st = update_slot st s e in
    let st = update_slot st s' e' in
    match get_slot st s2 with
    | None -> st
    | Some (VStoreE kv2 am2 l2 r2 p2) ->
      let p2new = s,d2 in
      let e2 = VStoreE kv2 am2 l2 r2 (Some p2new) in
      update_slot st s2 e2

let msp_store_post #vcfg (msp: madd_split_param vcfg) =
  apply_msp msp

let lemma_madd_to_store_split_identical_except #vcfg msp
  : Lemma (ensures (identical_except3 (msp_store_pre msp) (msp_store_post msp)
                                      (msp_slot msp) (msp_anc_slot msp) (msp_desc_slot msp)))
          [SMTPat (apply_msp #vcfg msp)] = ()


let is_nonedge #vcfg st (e: sds vcfg) =
  not (is_edge st e)

let msp_edge_post1 #vcfg msp: (e:sds vcfg {is_edge (msp_store_post msp) e}) =
  match msp with
  | MSP _ s  _ s' d _ -> s',d,s

let msp_edge_post2 #vcfg msp: (e: sds vcfg {is_edge (msp_store_post msp) e}) =
  let MSP _ s  _ _ _ d2 = msp in
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

let msp_parent_of_added #vcfg (msp: madd_split_param vcfg)
  : Lemma (ensures (let s = msp_slot msp in
                    let st = msp_store_post msp in
                    has_parent st s /\ parent_slot st s = msp_anc_slot msp)) =
  msp_anc_slot_not_added_slot msp;
  msp_desc_slot_not_added_slot msp

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

(* if s1 and s2 point to s, then it should be the case the s1 = s2 *)
let lemma_points_to_uniq #vcfg (st: vstore vcfg) s1 s2 s:
  Lemma (requires (points_to st s1 s /\ points_to st s2 s))
        (ensures (s1 = s2)) =
  assert(points_to_inuse_local st s1 s);
  assert(points_to_inuse_local st s2 s);
  ()

(* s cannot point to the same slot in both left and right directions *)
let lemma_points_distinct #vcfg (st: vstore vcfg) s:
  Lemma (requires (points_to_info st s Left = points_to_info st s Right))
        (ensures (points_to_none st s Left /\ points_to_none st s Right)) =
  if points_to_none st s Left then ()
  else (
    let sd = pointed_slot st s Left in
    // assert(points_to_dir st s Right sd);
    assert(points_to_inuse_local st s sd);
    ()
  )

let msp_points_to_desc_slot #vcfg msp s1 d1:
  Lemma (ensures (let stn = msp_store_post msp in
                  let sd = msp_desc_slot msp in
                  let e = s1,d1,sd in
                  is_edge stn e ==> e = msp_edge_post2 #vcfg msp)) =
  let stn = msp_store_post msp in
  let stp = msp_store_pre msp in
  let sd = msp_desc_slot msp in
  let e = s1,d1,sd in
  let d = msp_dir msp in
  let s' = msp_anc_slot msp in
  if not (is_edge stn e) || e = msp_edge_post2 msp then ()
  else (
    assert(s1 <> msp_slot msp);
    assert(is_edge stp e);
    assert(points_to_inuse_local stp s1 sd);
    assert(madd_props_local stp sd);
    assert(points_to_dir stp s1 d1 sd);
    assert(points_to_dir stp s' d sd);
    lemma_points_to_uniq stp s1 s' sd;

    // assert(s1 = s');

    ()
  )

let lemma_madd_to_store_split_points_to_inuse #vcfg msp:
  Lemma (ensures (points_to_inuse (msp_store_post msp)))
        [SMTPat (apply_msp #vcfg msp)] =
  let stn = msp_store_post msp in
  let stp = msp_store_pre msp in
  let s' = msp_anc_slot msp in
  let d2 = msp_dir2 msp in
  let sd = msp_desc_slot msp in
  assert(points_to_inuse_local stp s' sd);
  let aux s1 s2: Lemma (ensures (points_to_inuse_local stn s1 s2)) [SMTPat (points_to_inuse_local stn s1 s2)] =
    assert(points_to_inuse_local stp s1 s2);
    if not (points_to stn s1 s2) then ()
    else (
      let d12 = pointed_dir stn s1 s2 in

      if s1 = msp_slot msp then
        msp_added_slot_points_to msp s2 d12
      else if s1 = s' then ()
      else if s1 = sd then ()
      else
        ()
    )
  in
  ()

let lemma_madd_to_store_split_parent_props #vcfg msp:
  Lemma (ensures (parent_props (msp_store_post msp)))
        [SMTPat (apply_msp #vcfg msp)] =
  let stn = msp_store_post msp in
  let stp = msp_store_pre msp in

  msp_anc_slot_not_added_slot msp;
  msp_desc_slot_not_added_slot msp;
  msp_anc_slot_not_desc_slot msp;

  let aux s1 : Lemma (ensures (parent_props_local stn s1)) [SMTPat (parent_props_local stn s1)] =
    assert(parent_props_local stp s1);
    if empty_slot stn s1 || not (has_parent stn s1) then ()
    else if s1 = msp_slot msp then
      msp_parent_of_added msp
    else if s1 = msp_anc_slot msp then ()
    else if s1 = msp_desc_slot msp then
      assert(points_to_inuse_local stp (msp_anc_slot msp) s1)
    else
      ()
  in
  ()

let lemma_madd_to_store_split_madd_props #vcfg msp:
  Lemma (ensures (madd_props (msp_store_post msp)))
        [SMTPat (apply_msp #vcfg msp)] =
  let stn = msp_store_post msp in
  let stp = msp_store_pre msp in
  msp_anc_slot_not_added_slot msp;
  msp_desc_slot_not_added_slot msp;
  msp_anc_slot_not_desc_slot msp;

  let aux s1 : Lemma (ensures (madd_props_local stn s1)) [SMTPat (madd_props_local stn s1)] =
    assert(madd_props_local stp s1);
    if empty_slot stn s1 || add_method_of stn s1 <> Spec.MAdd || stored_base_key stn s1 = Root then ()
    else if s1 = msp_slot msp then ()
    else if s1 = msp_anc_slot msp then ()
    else if s1 = msp_desc_slot msp then ()
    else
      ()
  in
  ()

let lemma_madd_to_store_split_no_self_edge #vcfg msp:
  Lemma (ensures (no_self_edge (msp_store_post msp)))
        [SMTPat (apply_msp #vcfg msp)] =
  let stn = msp_store_post msp in
  let stp = msp_store_pre msp in
  msp_anc_slot_not_added_slot msp;
  msp_desc_slot_not_added_slot msp;
  msp_anc_slot_not_desc_slot msp;

  let aux s1 : Lemma (ensures (no_self_edge_local stn s1)) [SMTPat (no_self_edge_local stn s1)] =
    assert(no_self_edge_local stp s1);
    if not (points_to stn s1 s1) then ()
    else (
      let d1 = pointed_dir stn s1 s1 in
      if s1 = msp_slot msp then ()
      else if s1 = msp_anc_slot msp then ()
      else if s1 = msp_desc_slot msp then ()
      else
        ()
    )
  in
  ()

let madd_to_store_split
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:empty_slot_id st)
  (r: record vcfg.app)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_some_slot st s' d})
  (d2:bin_tree_dir)
  : Tot (st': vstore vcfg{let od = other_dir d in
                          let s2 = pointed_slot st s' d in
                          let od2 = other_dir d2 in
                          let k,v = r in

                          // st and st' identical except at s, s'
                          identical_except3 st st' s s' s2 /\

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
                          points_to_dir st' s d2 s2 /\
                          has_parent st' s /\
                          parent_slot st' s = s' /\
                          parent_dir st' s = d /\

                          has_parent st' s2 /\
                          parent_slot st' s2 = s /\
                          parent_dir st' s2 = d2 /\
                          inuse_slot st' s2 /\ inuse_slot st s2 /\
                          (let VStoreE r2' am2' ld2' rd2' _  = get_inuse_slot st' s2 in
                           let VStoreE r2 am2 ld2 rd2 _ = get_inuse_slot st s2 in
                           r2 = r2' /\ am2 = am2' /\ ld2 = ld2' /\ rd2 = rd2')})
  = let msp = MSP st s r s' d d2 in
    msp_anc_slot_not_added_slot msp;
    msp_desc_slot_not_added_slot msp;
    msp_anc_slot_not_desc_slot msp;
    apply_msp #vcfg msp

noeq type madd_root_param (vcfg: verifier_config) =
  | MSR: st: vstore vcfg ->
         s: empty_slot_id st ->
         v: value vcfg.app {IntV? v} ->
         madd_root_param vcfg

let madd_to_store_root_raw #vcfg (msr: madd_root_param vcfg): vstore_raw vcfg =
  match msr with
  | MSR st s v ->
    let e = VStoreE (IntK Root, v) Spec.MAdd None None None in
    update_slot st s e

let msr_store_pre #vcfg (msr: madd_root_param vcfg) =
  MSR?.st msr

let msr_store_post #vcfg msr =
  madd_to_store_root_raw #vcfg msr

let msr_slot #vcfg msr: slot_id vcfg =
  match msr with
  | MSR _ s _ -> s

let msr_value #vcfg (msr: madd_root_param vcfg)
  = match msr with
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

let lemma_madd_to_store_root_parent_props #vcfg msr:
  Lemma (ensures (parent_props (msr_store_post msr)))
        [SMTPat (madd_to_store_root_raw #vcfg msr)] =
  let stn = msr_store_post msr in
  let stp = msr_store_pre msr in
  let aux s1 : Lemma (ensures (parent_props_local stn s1)) [SMTPat (parent_props_local stn s1)] =
    assert(parent_props_local stp s1);
    ()
  in
  ()

let lemma_madd_to_store_root_madd_props #vcfg msr:
  Lemma (ensures (madd_props (msr_store_post msr)))
        [SMTPat (madd_to_store_root_raw #vcfg msr)] =
  let stn = msr_store_post msr in
  let stp = msr_store_pre msr in
  let aux s1 : Lemma (ensures (madd_props_local stn s1)) [SMTPat (madd_props_local stn s1)] =
    assert(madd_props_local stp s1);
    ()
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
  (v: value vcfg.app {IntV? v})
  : Tot (st':vstore vcfg{let r = IntK Root, v in
                         // st and st' identical except at s, s'
                         identical_except st st' s /\

                         // slot s contains (Root, v, MAdd) and points to none
                         inuse_slot st' s /\
                         get_inuse_slot st' s = VStoreE r Spec.MAdd None None None})
  = madd_to_store_root_raw (MSR st s v)

noeq type badd_param (vcfg: verifier_config)  =
  | BAS: st: vstore vcfg ->
         s: empty_slot_id st ->
         r: record vcfg.app ->
         badd_param vcfg

let apply_bas #vcfg (bas: badd_param vcfg) =
  match bas with
  | BAS st s kv ->
    let e = VStoreE kv Spec.BAdd None None None in
    update_slot st s e

let bas_store_pre #vcfg (bas: badd_param vcfg) =
  BAS?.st bas

let bas_store_post #vcfg bas =
  apply_bas #vcfg bas

let bas_record #vcfg (bas: badd_param vcfg) =
  BAS?.r bas

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

let lemma_bas_parent_props #vcfg bas:
  Lemma (ensures (parent_props (bas_store_post bas)))
        [SMTPat (apply_bas #vcfg bas)] =
  let stn = bas_store_post bas in
  let stp = bas_store_pre bas in
  let aux s1 : Lemma (ensures (parent_props_local stn s1)) [SMTPat (parent_props_local stn s1)] =
    assert(parent_props_local stp s1);
    ()
  in
  ()

let lemma_bas_madd_props #vcfg bas:
  Lemma (ensures (madd_props (bas_store_post bas)))
        [SMTPat (apply_bas #vcfg bas)] =
  let stn = bas_store_post bas in
  let stp = bas_store_pre bas in
  let aux s1 : Lemma (ensures (madd_props_local stn s1)) [SMTPat (madd_props_local stn s1)] =
    assert(madd_props_local stp s1);
    ()
  in
  ()

let badd_to_store
      (#vcfg:verifier_config)
      (st:vstore vcfg)
      (s:empty_slot_id st)
      (r: record vcfg.app)
  : Tot (st':vstore vcfg {// st and st' identical except for s
                          identical_except st st' s /\
                          inuse_slot st' s /\
                          get_inuse_slot st' s = VStoreE r Spec.BAdd None None None})
  = let bas = BAS st s r in
    apply_bas bas

noeq type mevict_param (vcfg: verifier_config) =
  | MEV: st:vstore vcfg ->
         s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right} ->
         s':inuse_slot_id st{s <> s'} ->
         d:bin_tree_dir{not (has_parent st s) /\ points_to_none st s' d \/
                  has_parent st s /\ parent_slot st s = s' /\ parent_dir st s = d} ->
         mevict_param vcfg

let apply_mev #vcfg (mev: mevict_param vcfg) =
  match mev with
  | MEV st s s' d ->
    let VStoreE kv' am' ld' rd' p' = get_inuse_slot st s' in
    let e' = if d = Left
             then VStoreE kv' am' None rd' p'
             else VStoreE kv' am' ld' None p' in
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
  has_parent (mev_store_pre #vcfg mev) (mev_slot mev)

let mev_deletes_edge_imply_parent_points #vcfg (mev: mevict_param vcfg)
  : Lemma (ensures (mev_deletes_edge mev = points_to_dir (mev_store_pre mev) (mev_anc_slot mev) (mev_dir mev) (mev_slot mev))) =
  assert(parent_props_local (mev_store_pre mev) (mev_slot mev));
  ()

let mev_deleted_edge #vcfg (mev: mevict_param vcfg {mev_deletes_edge mev}): sds vcfg =
  (mev_anc_slot mev), (mev_dir mev), (mev_slot mev)

let mev_deleted_edge_in_pre_not_in_post #vcfg (mev: mevict_param vcfg {mev_deletes_edge mev})
  : Lemma (ensures (let e = mev_deleted_edge mev in
                    is_edge (mev_store_pre mev) e /\
                    is_nonedge (mev_store_post mev) e))
          [SMTPat (apply_mev mev)] =
  let e = mev_deleted_edge mev in
  mev_deletes_edge_imply_parent_points mev

let mev_edge_in_post_in_pre #vcfg mev e
  : Lemma (ensures (is_edge (mev_store_post #vcfg mev) e ==>
                    is_edge (mev_store_pre mev) e)) = ()

let mev_edge_in_pre_in_post #vcfg mev e
  : Lemma (requires (is_edge (mev_store_pre #vcfg mev) e /\
                     (mev_deletes_edge mev ==> e <> mev_deleted_edge mev)))
          (ensures (is_edge (mev_store_post mev) e)) =
  let s1,d2,s2 = e in
  mev_deletes_edge_imply_parent_points mev;
  if s1 = mev_anc_slot mev then (
    if mev_deletes_edge mev then (
      assert(d2 <> mev_dir mev);
      ()
    )
    else ()
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
  let d = mev_dir mev in
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
      if s1 = mev_anc_slot mev then (
        assert(d12 <> d);
        ()
      )
      else (

        assert(get_slot stp s1 = get_slot stn s1);

        if s2 = mev_slot mev then (
          assert(points_to stp s1 s2);
          assert(points_to_inuse_local stp s1 s2);
          assert(has_parent stp s2)
        )
        else if s2 = mev_anc_slot mev then ()
        else
          assert(get_slot stp s2 = get_slot stn s2)
      )
    )
  in
  ()

let lemma_mev_parent_props #vcfg mev
  : Lemma (ensures (parent_props (mev_store_post mev)))
          [SMTPat (apply_mev #vcfg mev)] =
  let stp = mev_store_pre mev in
  let stn = mev_store_post mev in
  let aux s
    : Lemma (ensures (parent_props_local stn s)) [SMTPat (parent_props_local stn s)] =
    assert(parent_props_local stp s);
    if empty_slot stn s || not (has_parent stn s) then ()
    else if s = mev_anc_slot mev then ()
    else (
      assert(s <> mev_slot mev);
      assert(get_slot stp s = get_slot stn s);
      ()
    )
  in
  ()

let lemma_mev_madd_props #vcfg mev
  : Lemma (ensures (madd_props (mev_store_post mev)))
          [SMTPat (apply_mev #vcfg mev)] =
  let stp = mev_store_pre mev in
  let stn = mev_store_post mev in
  let aux s
    : Lemma (ensures (madd_props_local stn s)) [SMTPat (madd_props_local stn s)] =
    assert(madd_props_local stp s);
    if empty_slot stn s || add_method_of stn s <> Spec.MAdd || stored_base_key stn s = Root then ()
    else if s = mev_anc_slot mev then ()
    else (
      assert(s <> mev_slot mev);
      assert(get_slot stp s = get_slot stn s);
      ()
    )
  in
  ()

let lemma_mev_no_self_edges #vcfg mev
  : Lemma (ensures (no_self_edge (mev_store_post mev)))
          [SMTPat (apply_mev #vcfg mev)] =
  let stp = mev_store_pre mev in
  let stn = mev_store_post mev in
  let aux s
    : Lemma (ensures (no_self_edge_local stn s)) [SMTPat (no_self_edge_local stn s)] =
    assert(no_self_edge_local stp s);
    if not (points_to stn s s) then ()
    else (
      assert(s <> mev_slot mev);
      let d = pointed_dir stn s s in
      if s = mev_anc_slot mev then ()
      else
        ()
    )
  in
  ()

let mevict_from_store
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right})
  (s':inuse_slot_id st{s <> s'})
  (d:bin_tree_dir{not (has_parent st s) /\ points_to_none st s' d \/
                  has_parent st s /\ parent_slot st s = s' /\ parent_dir st s = d})
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
                          }) =
  let mev = MEV st s s' d in
  apply_mev mev

noeq type bevict_param (vcfg: verifier_config) =
  | BEV: st: vstore vcfg ->
         s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right /\ add_method_of st s = Spec.BAdd} ->
         bevict_param vcfg

let apply_bev #vcfg (bev: bevict_param vcfg) =
  match bev with
  | BEV st s ->
    Seq.upd st s None

let bev_store_post #vcfg bev = apply_bev #vcfg bev

let bev_store_pre #vcfg (bev: bevict_param vcfg): vstore vcfg =
  match bev with
  | BEV st _ -> st

let bev_slot #vcfg (bev: bevict_param vcfg): slot_id vcfg =
  match bev with
  | BEV _ s -> s

let lemma_bev_points_to_inuse #vcfg bev
  : Lemma (ensures (points_to_inuse (bev_store_post bev)))
          [SMTPat (apply_bev #vcfg bev)] =
  let stp = bev_store_pre bev in
  let stn = bev_store_post bev in

  let aux s1 s2
    : Lemma (ensures (points_to_inuse_local stn s1 s2)) [SMTPat (points_to_inuse_local stn s1 s2)] =
    assert(points_to_inuse_local stp s1 s2);
    if not (points_to stn s1  s2) then ()
    else ()
  in
  ()

let lemma_bev_parent_props #vcfg bev
  : Lemma (ensures (parent_props (bev_store_post bev)))
          [SMTPat (apply_bev #vcfg bev)] =
  let stp = bev_store_pre bev in
  let stn = bev_store_post bev in

  let aux s
    : Lemma (ensures (parent_props_local stn s)) [SMTPat (parent_props_local stn s)] =
    assert(parent_props_local stp s);
    ()
  in
  ()

let lemma_bev_madd_props #vcfg bev
  : Lemma (ensures (madd_props (bev_store_post bev)))
          [SMTPat (apply_bev #vcfg bev)] =
  let stp = bev_store_pre bev in
  let stn = bev_store_post bev in

  let aux s
    : Lemma (ensures (madd_props_local stn s)) [SMTPat (madd_props_local stn s)] =
    assert(madd_props_local stp s);
    ()
  in
  ()

let lemma_bev_no_self_edges #vcfg bev
  : Lemma (ensures (no_self_edge (bev_store_post bev)))
          [SMTPat (apply_bev #vcfg bev)] =
  let stp = bev_store_pre bev in
  let stn = bev_store_post bev in

  let aux s
    : Lemma (ensures (no_self_edge_local stn s)) [SMTPat (no_self_edge_local stn s)] =
    assert(no_self_edge_local stp s);
    ()
  in
  ()

let bevict_from_store
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right /\ add_method_of st s = Spec.BAdd})
  : Tot (st':vstore vcfg {// st and st' are identical except at slot s
                          identical_except st st' s /\

                          // slot s is empty after the update
                          empty_slot st' s})
  = apply_bev (BEV st s)

let pointing_slot (#vcfg:_)
                (st:vstore vcfg)
                (s:inuse_slot_id st{Root <> stored_base_key st s /\ add_method_of st s = Spec.MAdd})
 : Tot (s':inuse_slot_id st{points_to st s' s}) =
 assert(parent_props_local st s);
 assert(madd_props_local st s);
 parent_slot st s

let store_contains_key_prop (#vcfg:_) (st: vstore vcfg) (k: base_key)
  = exists (s: slot_id vcfg). (inuse_slot st s /\ stored_base_key st s = k)

#push-options "--fuel 0 --ifuel 1 --query_stats"

let rec find_aux (#vcfg:_) (st: vstore vcfg) (k: base_key) (s: nat{ s <= store_size vcfg })
  : Tot (o:option (slot_id vcfg) {match o with
                                  | None -> forall s'. (s' < s) ==> (stored_base_key st s' <> k)
                                  | Some s' -> s' < s /\ inuse_slot st s' /\
                                               stored_base_key st s' = k})
    (decreases s)
  = if s = 0 then None
    else
      let s' = s - 1 in
      if inuse_slot st s' && stored_base_key st s' = k then
        Some s'
      else
        let o = find_aux st k s' in
        if None = o then (
          let aux (sx:_)
            : Lemma (ensures (sx < s ==> stored_base_key st sx <> k))
            = ()
          in
          forall_intro aux;
          None
        )
        else o

#pop-options

let store_contains_key (#vcfg:_) (st:ismap_vstore vcfg) (k:base_key):
  b:bool{b <==> (exists (s: slot_id vcfg). inuse_slot st s /\ stored_base_key st s = k)}
  = let o = find_aux st k (store_size vcfg) in
    Some? o

let slot_of_key
  (#vcfg:_)
  (st:ismap_vstore vcfg)
  (k: base_key{store_contains_key st k})
  : Tot (s: inuse_slot_id st {k = stored_base_key st s})
  = Some?.v (find_aux st k (store_size vcfg))

(* updating a value preserves is_map *)
let lemma_ismap_update_value (#vcfg:verifier_config)
  (st:ismap_vstore vcfg)
  (s:inuse_slot_id st)
  (v:value vcfg.app {compatible (stored_key st s) v})
  : Lemma (ensures (is_map (update_value st s v)))
  = let st_ = update_value st s v in
    let aux (s1 s2:slot_id vcfg)
      : Lemma (ensures (inuse_slot st_ s1 ==>
                        inuse_slot st_ s2 ==>
                        s1 <> s2 ==>
                        stored_base_key st_ s1 <> stored_base_key st_ s2))
      = if inuse_slot st_ s1 && inuse_slot st_ s2 && s1 <> s2 then
          eliminate
            forall (s1 s2:slot_id vcfg).
            (inuse_slot st s1 ==>
             inuse_slot st s2 ==>
             s1 <> s2 ==>
             stored_base_key st s1 <> stored_base_key st s2)
          with s1 s2
    in
    forall_intro_2 aux

let store_contains_inuse_slot_keys #vcfg (st: ismap_vstore vcfg) (s: inuse_slot_id st)
  : Lemma (ensures (store_contains_key st (stored_base_key st s))) =
  ()

let lemma_ismap_madd_to_store (#vcfg:_) (st:ismap_vstore vcfg)
  (s:empty_slot_id st)
  (r: record vcfg.app)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_none st s' d})
  : Lemma (requires (let bk = to_base_key (key_of r) in
                     not (store_contains_key st bk)))
          (ensures (is_map (madd_to_store st s r s' d)))
  = let st_ = madd_to_store st s r s' d in
    let aux (s1 s2: slot_id vcfg)
      : Lemma (ensures (inuse_slot st_ s1 ==>
                        inuse_slot st_ s2 ==>
                        s1 <> s2 ==>
                        stored_base_key st_ s1 <> stored_base_key st_ s2))
      = if inuse_slot st_ s1 && inuse_slot st_ s2 && s1 <> s2 then (
          eliminate
            forall (s1 s2:slot_id vcfg).
            (inuse_slot st s1 ==>
             inuse_slot st s2 ==>
             s1 <> s2 ==>
             stored_base_key st s1 <> stored_base_key st s2)
          with s1 s2;
          if s1 = s then
            store_contains_inuse_slot_keys st s2
          else if s2 = s then
            store_contains_inuse_slot_keys st s1
        )
    in
    forall_intro_2 aux

let lemma_ismap_madd_to_store_split
  (#vcfg: verifier_config)
  (st:ismap_vstore vcfg)
  (s:empty_slot_id st)
  (r: record vcfg.app)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_some_slot st s' d})
  (d2:bin_tree_dir)
  : Lemma (requires (let bk = to_base_key (key_of r) in
                     not (store_contains_key st bk)))
          (ensures (is_map (madd_to_store_split st s r s' d d2)))
  = let st_ = madd_to_store_split st s r s' d d2 in
    let aux (s1 s2: slot_id vcfg)
      : Lemma (ensures (inuse_slot st_ s1 ==>
                        inuse_slot st_ s2 ==>
                        s1 <> s2 ==>
                        stored_base_key st_ s1 <> stored_base_key st_ s2))
      = if inuse_slot st_ s1 && inuse_slot st_ s2 && s1 <> s2 then (
          eliminate
            forall (s1 s2:slot_id vcfg).
            (inuse_slot st s1 ==>
             inuse_slot st s2 ==>
             s1 <> s2 ==>
             stored_base_key st s1 <> stored_base_key st s2)
          with s1 s2;
          if s1 = s then
            store_contains_inuse_slot_keys st s2
          else if s2 = s then
            store_contains_inuse_slot_keys st s1
        )
    in
    forall_intro_2 aux

(* if two slots of an ismap store contain the same key, then the two slots should be identical *)
let lemma_ismap_correct (#vcfg:_) (st:ismap_vstore vcfg) (s1 s2: inuse_slot_id st)
  : Lemma (requires (stored_base_key st s1 = stored_base_key st s2))
          (ensures (s1 = s2))
  = ()

let lemma_empty_store_is_map (#vcfg:_):
  Lemma (ensures (is_map (empty_store vcfg))) = ()

let lemma_empty_contains_nokey (#vcfg:_) (k:base_key):
  Lemma (ensures (let st = empty_store vcfg in
                  not (store_contains_key st k))) = ()

let lemma_madd_root_to_store_is_map
      (#vcfg:_)
      (st:ismap_vstore vcfg{not (store_contains_key st Root)})
      (s:empty_slot_id st)
      (v:value vcfg.app {IntV? v})
  : Lemma (ensures (is_map (madd_to_store_root st s v)))
  = let st_ = madd_to_store_root st s v in
    let aux (s1 s2: slot_id vcfg)
      : Lemma (ensures (inuse_slot st_ s1 ==>
                        inuse_slot st_ s2 ==>
                        s1 <> s2 ==>
                        stored_base_key st_ s1 <> stored_base_key st_ s2))
      = if inuse_slot st_ s1 && inuse_slot st_ s2 && s1 <> s2 then (
          eliminate
            forall (s1 s2:slot_id vcfg).
            (inuse_slot st s1 ==>
             inuse_slot st s2 ==>
             s1 <> s2 ==>
             stored_base_key st s1 <> stored_base_key st s2)
          with s1 s2;
          if s1 = s then
            store_contains_inuse_slot_keys st s2
          else if s2 = s then
            store_contains_inuse_slot_keys st s1
        )
    in
    forall_intro_2 aux

let lemma_not_contains_after_mevict
  (#vcfg: verifier_config)
  (st:ismap_vstore vcfg)
  (s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right})
  (s':inuse_slot_id st{s <> s'})
  (d:bin_tree_dir{not (has_parent st s) /\ points_to_none st s' d \/
                  has_parent st s /\ parent_slot st s = s' /\ parent_dir st s = d}):
  Lemma (ensures (let st' = mevict_from_store st s s' d in
                  let k = stored_base_key st s in
                  is_map st' /\
                  not (store_contains_key st' k)))
  = let st_ = mevict_from_store st s s' d  in
    let k = stored_base_key st s in
    let aux (s1 s2: slot_id vcfg)
      : Lemma (ensures (inuse_slot st_ s1 ==>
                        inuse_slot st_ s2 ==>
                        s1 <> s2 ==>
                        stored_base_key st_ s1 <> stored_base_key st_ s2))
      = if inuse_slot st_ s1 && inuse_slot st_ s2 && s1 <> s2 then (
          eliminate
            forall (s1 s2:slot_id vcfg).
            (inuse_slot st s1 ==>
             inuse_slot st s2 ==>
             s1 <> s2 ==>
             stored_base_key st s1 <> stored_base_key st s2)
          with s1 s2
        )
    in
    forall_intro_2 aux;
    assert(is_map st_);
    if store_contains_key st_ k then (
      let s1 = slot_of_key st_ k in
      assert(s1 <> s);
      assert(stored_base_key st s1 = k);
      ()
    )

let lemma_not_contains_after_bevict
  (#vcfg: verifier_config)
  (st:ismap_vstore vcfg)
  (s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right /\ add_method_of st s = Spec.BAdd})
  : Lemma (ensures (let st' = bevict_from_store st s in
                    let k = stored_base_key st s in
                    is_map st' /\
                    not (store_contains_key st' k)))
  = let st_ = bevict_from_store st s in
    let k = stored_base_key st s in
    let aux (s1 s2: slot_id vcfg)
      : Lemma (ensures (inuse_slot st_ s1 ==>
                        inuse_slot st_ s2 ==>
                        s1 <> s2 ==>
                        stored_base_key st_ s1 <> stored_base_key st_ s2))
      = if inuse_slot st_ s1 && inuse_slot st_ s2 && s1 <> s2 then (
          eliminate
            forall (s1 s2:slot_id vcfg).
            (inuse_slot st s1 ==>
             inuse_slot st s2 ==>
             s1 <> s2 ==>
             stored_base_key st s1 <> stored_base_key st s2)
          with s1 s2
        )
    in
    forall_intro_2 aux;
    assert(is_map st_);
    if store_contains_key st_ k then (
      let s1 = slot_of_key st_ k in
      assert(s1 <> s);
      assert(stored_base_key st s1 = k);
      ()
    )

let lemma_ismap_badd_to_store (#vcfg:_) (st:ismap_vstore vcfg)
  (s:empty_slot_id st)
  (r: record vcfg.app)
  : Lemma (requires (let bk = to_base_key (key_of r) in
                     not (store_contains_key st bk)))
          (ensures (is_map (badd_to_store st s r)))
  = let st_ = badd_to_store st s r in

    let aux (s1 s2: slot_id vcfg)
      : Lemma (ensures (inuse_slot st_ s1 ==>
                        inuse_slot st_ s2 ==>
                        s1 <> s2 ==>
                        stored_base_key st_ s1 <> stored_base_key st_ s2))
      = if inuse_slot st_ s1 && inuse_slot st_ s2 && s1 <> s2 then (
          eliminate
            forall (s1 s2:slot_id vcfg).
            (inuse_slot st s1 ==>
             inuse_slot st s2 ==>
             s1 <> s2 ==>
             stored_base_key st s1 <> stored_base_key st s2)
          with s1 s2;
          if s1 = s then store_contains_inuse_slot_keys st s2
          else if s2 = s then store_contains_inuse_slot_keys st s1
        )
    in
    forall_intro_2 aux;
    ()

#push-options "--fuel 0 --ifuel 1 --query_stats"

let store_rel_slot (#vcfg:_) (st: ismap_vstore vcfg) (st':_ {store_rel st st'}) (s: inuse_slot_id st)
  : Lemma (ensures (let k = stored_base_key st s in
                    Spec.store_contains st' k /\
                    stored_key st s = Spec.stored_key st' k /\
                    stored_value st s = Spec.stored_value st' k /\
                    add_method_of st s = Spec.add_method_of st' k))
  = let k = stored_base_key st s in
    store_contains_inuse_slot_keys st s;
    lemma_ismap_correct st s (slot_of_key st k)

#pop-options
