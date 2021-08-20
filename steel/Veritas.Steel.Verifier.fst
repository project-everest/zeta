module Veritas.Steel.Verifier

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
open Steel.Array
open FStar.Ghost
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module T = Veritas.Formats.Types

open Veritas.Steel.VCache
open Veritas.Steel.VerifierModel
open Veritas.ThreadStateModel

let prf_set_hash = ref model_hash

let prf_set_hash_sl (x:prf_set_hash)
  = Steel.Memory.emp

let prf_set_hash_sel (r:prf_set_hash) : selector (model_hash) (prf_set_hash_sl r) = admit()

let prf_update_hash p r t thread_id = sladmit()

let update_clock (ts:T.timestamp) (vs:thread_state_t) = sladmit()

//Needs an unfold, else weirdness
unfold
let slot_ok (s:U16.t) (vs:_) (h:rmem (thread_state_inv vs))
  = U16.v s < length (v_thread vs h).model_store

assume
val points_to_some_slot (s:U16.t)
                        (d:bool)
                        (vs:_)
  : Steel bool
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> U16.v s < length (v_thread vs h).model_store)
    (ensures fun h0 b h1 ->
      U16.v s < length (v_thread vs h0).model_store /\
      b == VerifierModel.points_to_some_slot (v_thread vs h0) s d /\
      v_thread vs h0 == v_thread vs h1)

assume
val madd_to_store (s:U16.t) (k:T.key) (v:T.value) (s':U16.t) (d:bool)
                  (vs:_)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 ->
      slot_ok s vs h0 /\
      slot_ok s' vs h0)
    (ensures fun h0 _ h1 ->
      slot_ok s vs h0 /\
      slot_ok s' vs h0 /\
      v_thread vs h1 == model_madd_to_store (v_thread vs h0) s k v s' d)

assume
val madd_to_store_split (s:U16.t) (k:T.key) (v:T.value) (s':U16.t) (d d':bool)
                        (vs:_)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 ->
      slot_ok s vs h0 /\
      slot_ok s' vs h0)
    (ensures fun h0 _ h1 ->
      slot_ok s vs h0 /\
      slot_ok s' vs h0 /\
      v_thread vs h1 == model_madd_to_store_split (v_thread vs h0) s k v s' d d')

assume
val vevictb_update_hash_clock
       (s:U16.t)
       (t:T.timestamp)
       (vs:_)
   : Steel unit
     (thread_state_inv vs)
     (fun _ -> thread_state_inv vs)
     (requires fun h0 ->
       U16.v s < length (v_thread vs h0).model_store /\
       VerifierModel.sat_evictb_checks (v_thread vs h0) s t)
     (ensures fun h0 _ h1 ->
       U16.v s < length (v_thread vs h0).model_store /\
       VerifierModel.sat_evictb_checks (v_thread vs h0) s t /\
       v_thread vs h1 ==
       model_vevictb_update_hash_clock (v_thread vs h0) s t)

assume
val bevict_from_store (s:U16.t) (vs:_)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 ->
       U16.v s < length (v_thread vs h0).model_store)
    (ensures fun h0 _ h1 ->
       U16.v s < length (v_thread vs h0).model_store /\
       v_thread vs h1 ==
       model_bevict_from_store (v_thread vs h0) s)

assume
val update_value (s:U16.t) (v:T.value) (vs:_)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 ->
      U16.v s  < length (v_thread vs h0).model_store /\
      has_slot (v_thread vs h0) s /\
      is_value_of (key_of_slot (v_thread vs h0) s) v)
    (ensures fun h0 _ h1 ->
      U16.v s  < length (v_thread vs h0).model_store /\
      has_slot (v_thread vs h0) s /\
      is_value_of (key_of_slot (v_thread vs h0) s) v /\
      v_thread vs h1 == model_update_value (v_thread vs h0) s v)

assume
val mevict_from_store (s s':_) (d:_) (vs:_)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 ->
       U16.v s < length (v_thread vs h0).model_store /\
       U16.v s' < length (v_thread vs h0).model_store)
    (ensures fun h0 _ h1 ->
       U16.v s < length (v_thread vs h0).model_store /\
       U16.v s' < length (v_thread vs h0).model_store /\
       v_thread vs h1 ==
       model_mevict_from_store (v_thread vs h0) s s' d)

#push-options "--query_stats --fuel 0 --ifuel 1"
let fail vs msg = write vs.failed true; ()

let vget (s:U16.t) (k:T.key) (v:T.data_value) (vs: thread_state_t)
  = let ro = VCache.vcache_get_record vs.st s in
    match ro with
    | None ->
      fail vs "Slot not found"
    | Some r' ->
      if k <> r'.record_key
      then fail vs "Failed: inconsistent key in Get"
      else if T.V_dval v <> r'.record_value
      then fail vs "Failed: inconsistent value in Get"
      // AF: Usual problem of Steel vs SteelF difference between the two branches
      else (noop (); ())

(* verifier write operation *)
let vput s k v vs
  = let ro = VCache.vcache_get_record vs.st s in
    match ro with
    | None ->
      fail vs "Slot not found"

    | Some r ->
      if r.record_key <> k then fail vs "slot-key mismatch"
      else if not (is_data_key k) then fail vs "not a data key"
      else (
        vcache_update_record vs.st s ({ r with record_value = T.V_dval v });
        () //seem to need this
      )

let coerce #a #p (x:a) (pf:squash (p x)) : x:a{p x} = x

let vaddm s r s' vs
  = let h = get () in
    assert (U16.v s  < length (v_thread vs h).model_store);  //this assert seems necessary
    let k = r.T.record_key in
    let v = r.T.record_value in
    (* check store contains slot s' *)
    let r' = VCache.vcache_get_record vs.st s' in
    match r' with
    | None -> fail vs "Slot missing"
    | Some r' ->
      let k' = r'.record_key in
      let v' = r'.record_value in
      (* check k is a proper desc of k' *)
      if not (is_proper_descendent k k') then fail vs "not proper descendent"
      (* check store does not contain slot s *)
      else (
        let r_old = VCache.vcache_get_record vs.st s in
        if Some? r_old then fail vs "old record exists"
        else if not (is_value_of k v) then fail vs "incompatible value for key"
        else let Some v' = to_merkle_value v' in
             let d = desc_dir k k' in
             let dh' = desc_hash_dir v' d in
             let h = hashfn v in
             match dh' with
             | T.Dh_vnone _ -> (* k' has no child in direction d *)
             (* first add must be init value *)
               if v <> init_value k then fail vs "incorrect initial value"
               else let b = points_to_some_slot s' d vs in
                    if b then fail vs "points to some slot"
                    else (
                      let tsm = madd_to_store s k v s' d vs in
                      let v'_upd = update_merkle_value v' d k h false in
                      update_value s' (T.V_mval v'_upd) vs
                    )

        | T.Dh_vsome {T.dhd_key=k2; T.dhd_h=h2; T.evicted_to_blum = b2} ->
          if k2 = k then (* k is a child of k' *)
            (* check hashes match and k was not evicted to blum *)
            if not (h2 = h && b2 = T.Vfalse) then fail vs "hash mismatch or evicted"
            (* check slot s' does not contain a desc along direction d *)
            else (
              let b = points_to_some_slot s' d vs in
              if b then fail vs "points to some slot"
              else madd_to_store s k v s' d vs
            )
          else (
            (* first add must be init value *)
            if v <> init_value k then fail vs "not init value"
            (* check k2 is a proper desc of k *)
            else
              let b = (is_proper_descendent k2 k) in
                if not b
                then fail vs "not proper descendent"
                else (
                  let pf : squash (is_proper_descendent k2 k) = () in
                  //need this weird coercion to avoid mysterious failures
                  let k : (k:T.key { is_proper_descendent k2 k }) = coerce k pf in
                  let d2 = desc_dir k2 k in
                  let Some mv = to_merkle_value v in
                  let mv_upd = update_merkle_value mv d2 k2 h2 (b2=T.Vtrue) in
                  let v'_upd = update_merkle_value v' d k h false in
                  let b = points_to_some_slot s' d vs in
                  //can't share the continuation
                  if b
                  then (
                    madd_to_store_split s k (T.V_mval mv_upd) s' d d2 vs;
                    update_value s' (T.V_mval v'_upd) vs
                  )
                  else (
                    madd_to_store s k (T.V_mval mv_upd) s' d vs;
                    update_value s' (T.V_mval v'_upd) vs
                  )
             )))

let vevictm s s' vs
  = let h = get () in
    assert (U16.v s  < length (v_thread vs h).model_store);  //this assert seems necessary
    if s = s' then fail vs "Equal slots"
    else (
      let r = VCache.vcache_get_record vs.st s in
      let r' = VCache.vcache_get_record vs.st s' in
      match r, r' with
      | None, _
      | _, None -> fail vs "Empty slots"
      | Some r, Some r' ->
        let k = r.record_key in
        let v = r.record_value in
        let k' = r'.record_key in
        let v' = r'.record_value in
        (* check k is a proper descendent of k' *)
        if not (is_proper_descendent k k') then fail vs "Not proper descendent"
        (* check k does not have a (merkle) child in the store *)
        else
          let b1 = points_to_some_slot s true vs in
          let b2 = points_to_some_slot s false vs in
          if b1 || b2
          then fail vs "Points to some slot"
          else (
            let d = desc_dir k k' in
            let Some v' = to_merkle_value v' in
            let dh' = desc_hash_dir v' d in
            match dh' with
            | T.Dh_vnone _ -> fail vs "No child"
            | T.Dh_vsome {T.dhd_key=k2; T.dhd_h=h2; T.evicted_to_blum = b2} ->
              if k2 <> k then fail vs "k2 <> k"
              else if Some? r.record_parent_slot &&
                    (fst (Some?.v r.record_parent_slot) <> s' ||
                     snd (Some?.v r.record_parent_slot) <> d)
              then fail vs "parent slot mismatch"
              else let b = points_to_some_slot s' d vs in
                   if None? r.record_parent_slot
                   && b
                   then fail vs "parent slot mismatch"
                   else (
                     let h = hashfn v in //Lower
                     let v'_upd = update_merkle_value v' d k h false in
                     let tsm = update_value s' (T.V_mval v'_upd) vs in
                     mevict_from_store s s' d vs
                   )
          ))

let vaddb s r t thread_id vs
  = let h = get() in
    assert (U16.v s < length (v_thread vs h).model_store);

    let { T.record_key = k;
          T.record_value = v } = r in
    (* check value type consistent with key k *)
    if not (is_value_of k v)
    then (
      fail vs "vaddb: value is incompatible with key"
    )
    else (
      let ro = VCache.vcache_get_record vs.st s in
      if Some? ro
      then (
        fail vs "vaddb: slot s already exists"
      )
      else (
        prf_update_hash vs.hadd r t thread_id;// vs;
        update_clock t vs;
        VCache.vcache_add_record vs.st s k v T.BAdd)
    )

val sat_evictb_checks (s:U16.t)
                      (t:T.timestamp)
                      (vs:_)
  : Steel bool
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> U16.v s < length (v_thread vs h).model_store)
    (ensures fun h0 b h1 ->
      U16.v s < length (v_thread vs h0).model_store /\
      b == VerifierModel.sat_evictb_checks (v_thread vs h0) s t /\
      v_thread vs h0 == v_thread vs h1)
let sat_evictb_checks s t vs
  = let ro = VCache.vcache_get_record vs.st s in
    match ro with
    | None -> Steel.Effect.Atomic.return false
    | Some r ->
      let clk = read vs.clock in
      if is_root r.record_key
      then Steel.Effect.Atomic.return false
      else if not (clk `timestamp_lt` t)
      then Steel.Effect.Atomic.return false
      else (
        let b1 = points_to_some_slot s true vs in
        let b2 = points_to_some_slot s false vs in
        not b1 && not b2
      )

let vevictb (s:U16.t)
            (t:T.timestamp)
            (vs:thread_state_t)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> U16.v s < length (v_thread vs h).model_store)
    (ensures  fun h0 _ h1 ->
      U16.v s < length (v_thread vs h0).model_store /\
      v_thread vs h1 == vevictb_model (v_thread vs h0) s t)
  = let chk = sat_evictb_checks s t vs in
    if not chk then fail vs "sat_evictb_checks failed"
    else (
      let Some r = VCache.vcache_get_record vs.st s in
      if r.record_add_method <> T.BAdd
      then fail vs "Record is not a BAdd"
      else (
        vevictb_update_hash_clock s t vs;
        bevict_from_store s vs
      )
    )

let vevictbm (s s':U16.t)
             (t:T.timestamp)
             (vs:_)
  = let h = get() in
    assert (U16.v s < length (v_thread vs h).model_store);
    assert (U16.v s' < length (v_thread vs h).model_store);
    if s = s' then fail vs "equal slots"
    else (
      let b = sat_evictb_checks s t vs in
      if not b then fail vs "sat_evictb_checks"
      else (
        let r' = VCache.vcache_get_record vs.st s' in
        if None? r' then fail vs "s' does not exist"
        else (
          let r = VCache.vcache_get_record vs.st s in
          let Some r = r in
          let Some r' = r' in
          if r.record_add_method <> T.MAdd
          then fail vs "not MAdd"
          else (
            let k = r.record_key in
            let k' = r'.record_key in
            let v' = r'.record_value in
            if not (is_proper_descendent k k')
            then fail vs "not proper desc"
            else (
              let Some mv' = to_merkle_value v' in
              let d = desc_dir k k' in
              let dh' = desc_hash_dir mv' d in
              match dh' with
              | T.Dh_vnone _ ->
                fail vs "dh' none"
              | T.Dh_vsome {T.dhd_key=k2; T.dhd_h=h2; T.evicted_to_blum = b2} ->
                if (k2 <> k) || (b2 = T.Vtrue)
                then fail vs "k2<>k || b2"
                else if None? r.record_parent_slot
                     || fst (Some?.v r.record_parent_slot) <> s'
                     || snd (Some?.v r.record_parent_slot) <> d
                then fail vs "paren slot checks"
                else (
                  vevictb_update_hash_clock s t vs;
                  let mv'_upd = update_merkle_value mv' d k h2 true in
                  update_value s' (T.V_mval mv'_upd) vs;
                  mevict_from_store s s' d vs
                )
            )
        )
      )
    )
  )
