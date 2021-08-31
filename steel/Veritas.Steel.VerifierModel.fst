module Veritas.Steel.VerifierModel

open FStar.Ghost
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module VSeq = Veritas.SeqAux

module MSH = Veritas.MultiSetHashDomain
module T = Veritas.Formats.Types
open Veritas.ThreadStateModel

let model_fail tsm = {tsm with model_failed=true}

let model_get_record (tsm:thread_state_model) (s:slot tsm.model_store_len)
  : GTot (option (record tsm.model_store_len))
  = Seq.index tsm.model_store (U16.v s)

let has_slot (tsm:thread_state_model) (s:slot tsm.model_store_len)
  = Some? (model_get_record tsm s)

let model_put_record (tsm:thread_state_model) (s:slot tsm.model_store_len) (r:record tsm.model_store_len)
  : thread_state_model
  = {tsm with model_store=Seq.upd tsm.model_store (U16.v s) (Some r)}

let key_of_slot (tsm:thread_state_model) (s:slot tsm.model_store_len { has_slot tsm s })
  : GTot T.key
  = let Some v = model_get_record tsm s in
    v.record_key

let model_update_value (tsm:thread_state_model)
                       (s:slot tsm.model_store_len{has_slot  tsm s})
                       (r:T.value {is_value_of (key_of_slot tsm s) r})
  : thread_state_model
  = let Some v = model_get_record tsm s in
    model_put_record tsm s ({v with record_value = r})

let model_evict_record (tsm:thread_state_model) (s:slot tsm.model_store_len)
  : thread_state_model
  = {tsm with model_store=Seq.upd tsm.model_store (U16.v s) None }

module TSM = Veritas.ThreadStateModel
let mk_record_full (#n:_)
                   (k:T.key)
                   (v:T.value{is_value_of k v})
                   (a:T.add_method)
                   (l r:option (TSM.slot n))
                   (p:option (TSM.slot n & bool))
  : TSM.record n
  = {
      record_key = k;
      record_value = v;
      record_add_method = a;
      record_l_child_in_store = l;
      record_r_child_in_store = r;
      record_parent_slot = p
    }


let mk_record #n (k:T.key) (v:T.value{is_value_of k v}) (a:T.add_method) : record n
  = mk_record_full k v a None None None

let model_update_clock (tsm:thread_state_model) (ts:T.timestamp)
  : thread_state_model
  = if FStar.UInt.fits (U64.v tsm.model_clock + U64.v ts) 64
    then { tsm with model_clock = tsm.model_clock `U64.add` ts } //+1
    else model_fail tsm

let model_update_hash (h:model_hash) (r:T.record) (t:T.timestamp) (thread_id:T.thread_id)
  : model_hash
  = let open Veritas.ThreadStateModel in
    match lift_key r.T.record_key, lift_value r.T.record_value with
    | Some k, Some v ->
      Veritas.MultiSetHash.ms_hashfn_upd
        (Veritas.MultiSetHashDomain.MHDom (k, v) (timestamp_of_clock t) (U16.v thread_id))
        h
    | _ ->
      //TODO: we need a better spec here, otherwise prf_update_hash will not be provable
      h

let model_update_hadd (tsm:_) (r:T.record) (t:T.timestamp) (thread_id:T.thread_id) =
  ({tsm with model_hadd = model_update_hash tsm.model_hadd r t thread_id})

let model_update_hevict (tsm:_) (r:T.record) (t:T.timestamp) (thread_id:T.thread_id) =
  ({tsm with model_hevict = model_update_hash tsm.model_hevict r t thread_id})

module TSM = Veritas.ThreadStateModel
module C = FStar.Int.Cast
let shift_right_64 (x:U64.t) (w:U16.t{U16.v w <= 64})
  : U64.t
  = if w = 64us then 0uL
    else U64.shift_right x (C.uint16_to_uint32 w)

let truncate_key (k:T.key) (w:U16.t { U16.v w < U16.v k.T.significant_digits }) =
  let open U16 in
  let kk =
    let kk = k.T.k in
    let zkey = { T.v0 = 0uL; T.v1 = 0uL; T.v2 = 0uL; T.v3 = 0uL } in
    if w <=^ 64us
    then { zkey with T.v0 = shift_right_64 kk.T.v0 (64us -^ w) }
    else if w <=^ 128us
    then { zkey with T.v0 = kk.T.v0;
                     T.v1 = shift_right_64 kk.T.v1 (128us -^ w) }
    else if w <^ 192us
    then { kk with T.v2 = shift_right_64 kk.T.v2 (192us -^ w); T.v3 = 0uL }
    else { kk with T.v3 = shift_right_64 kk.T.v3 (256us -^ w) }
  in
  { k with T.k = kk; T.significant_digits = w }

let is_proper_descendent (k0 k1:T.key)
  : bool
  = let open FStar.UInt16 in
    k0.T.significant_digits >^ k1.T.significant_digits &&
    truncate_key k0 k1.T.significant_digits = k1

let is_proper_descendent_key_type (k0 k1:T.key)
  : Lemma
    (requires is_proper_descendent k0 k1)
    (ensures  not (is_data_key k1))
    [SMTPat (is_proper_descendent k0 k1)]
  = ()

let ith_bit (k0:T.key) (i:U16.t { U16.v i < 256 })
  : bool
  = let open U16 in
    let kk = k0.T.k in
    if i <^ 64us
    then (U64.shift_right kk.T.v0 (C.uint16_to_uint32 i)) `U64.rem` 2uL = 1uL
    else if i <^ 128us
    then (U64.shift_right kk.T.v1 (C.uint16_to_uint32 (i -^ 64us))) `U64.rem` 2uL = 1uL
    else if i <^ 192us
    then (U64.shift_right kk.T.v2 (C.uint16_to_uint32 (i -^ 128us))) `U64.rem` 2uL = 1uL
    else (U64.shift_right kk.T.v3 (C.uint16_to_uint32 (i -^ 192us))) `U64.rem` 2uL = 1uL

let desc_dir (k0:T.key) (k1:T.key { k0 `is_proper_descendent` k1 })
  : bool
  = let open U16 in
    ith_bit k0 k1.T.significant_digits

let to_merkle_value (v:T.value)
  : option T.mval_value
  = match v with
    | T.V_mval v -> Some v
    | _ -> None

let desc_hash_dir (v:T.mval_value) (d:bool)
  : T.descendent_hash
  = if d then v.T.l else v.T.r

let update_merkle_value (v:T.mval_value)
                        (d:bool)
                        (k:T.key)
                        (h:T.hash_value)
                        (b:bool)
  : T.mval_value
  = let desc_hash = T.(Dh_vsome ({
        dhd_key = k;
        dhd_h = h;
        evicted_to_blum = (if b then Vtrue else Vfalse)
    })) in
    if d then {v with T.l = desc_hash}
    else {v with T.r = desc_hash}

let hashfn (v:T.value)
  : T.hash_value
  = admit()

let init_value (k:T.key)
  : T.value
  = let open T in
    if TSM.is_data_key k
    then V_dval (Dv_vnone ())
    else V_mval ({ l = Dh_vnone (); r = Dh_vnone ()})

let points_to_some_slot (tsm:thread_state_model)
                        (s:slot tsm.model_store_len)
                        (d:bool)
  : GTot bool
  = match model_get_record tsm s with
    | None -> false
    | Some r ->
      if d
      then Some? (r.TSM.record_l_child_in_store)
      else Some? (r.TSM.record_r_child_in_store)

let model_madd_to_store (tsm:thread_state_model)
                        (s:slot tsm.model_store_len)
                        (k:T.key)
                        (v:T.value)
                        (s':slot tsm.model_store_len)
                        (d:bool)
  : tsm':thread_state_model{
        Seq.length tsm.model_store = Seq.length tsm'.model_store /\
        (forall (ss:slot tsm.model_store_len). {:pattern has_slot tsm' ss}
          has_slot tsm ss ==>
          (has_slot tsm' ss /\
           is_data_key (key_of_slot tsm ss) ==
           is_data_key (key_of_slot tsm' ss)))
    }
  = let open TSM in
    if has_slot tsm s
    || not (is_value_of k v)
    || not (has_slot tsm s')
    then tsm
    else
      let Some r' = model_get_record tsm s' in
      let new_entry = {
        record_key = k;
        record_value = v;
        record_add_method = T.MAdd;
        record_l_child_in_store = None;
        record_r_child_in_store = None;
        record_parent_slot = Some (s', d)
      } in
      let store' = Seq.upd tsm.model_store (U16.v s) (Some new_entry) in
      let r' =
        if d
        then { r' with record_l_child_in_store = Some s }
        else { r' with record_r_child_in_store = Some s }
      in
      let store'' = Seq.upd store' (U16.v s') (Some r') in
      {tsm with model_store = store''}

let record_update_parent_slot (#n:_)
                              (r:record n)
                              (s:(slot n & bool))
  = { r with record_parent_slot = Some s }

let record_update_child (#n:_) (r:record n) (d:bool) (s:slot n)
  : record n
  = if d then {r with record_l_child_in_store = Some s }
    else {r with record_r_child_in_store = Some s}

let record_child_slot (#n:_) (r:record n) (d:bool)
  : option (slot n)
  = if d then r.record_l_child_in_store
    else r.record_r_child_in_store

let model_madd_to_store_split (tsm:thread_state_model)
                              (s:slot tsm.model_store_len)
                              (k:T.key)
                              (v:T.value)
                              (s':slot tsm.model_store_len)
                              (d d2:bool)
  : tsm':thread_state_model{
         Seq.length tsm.model_store = Seq.length tsm'.model_store /\
         (forall (ss:slot tsm.model_store_len). {:pattern has_slot tsm' ss}
           (has_slot tsm ss ==>
             (has_slot tsm' ss /\
              is_data_key (key_of_slot tsm ss) ==
              is_data_key (key_of_slot tsm' ss))))}
  = let open TSM in
    let st = tsm.model_store in
    if has_slot tsm s
    || not (is_value_of k v)
    || not (has_slot tsm s')
    then tsm
    else
      match model_get_record tsm s' with
      | Some r' ->
        let p = (s', d) in
        let s2_opt = record_child_slot r' d in
        match s2_opt with
        | None -> tsm //fail
        | Some s2 ->
          if U16.v s2 >= Seq.length st
          then tsm //fail
          else match Seq.index st (U16.v s2) with
               | None -> tsm
               | Some r2 ->
                 let e = mk_record_full k v T.MAdd None None (Some p) in
                 let e = record_update_child e d2 s2 in
                 let e' = record_update_child r' d s in
                 let p2new = s2, d2 in
                 let e2 = record_update_parent_slot r2 p2new in
                 let st = Seq.upd st (U16.v s) (Some e) in
                 let st = Seq.upd st (U16.v s') (Some e') in
                 let st = Seq.upd st (U16.v s2) (Some e2) in
                 { tsm with model_store = st }

let model_mevict_from_store (tsm:thread_state_model)
                            (s s':slot tsm.model_store_len)
                            (d:bool)
  : tsm':thread_state_model{
        Seq.length tsm.model_store = Seq.length tsm'.model_store
    }
  = let open TSM in
    match model_get_record tsm s' with
    | None -> tsm //fail
    | Some r' ->
      let e' =
        if d
        then { r' with record_l_child_in_store = None }
        else { r' with record_r_child_in_store = None }
      in
      let st = Seq.upd tsm.model_store (U16.v s') (Some e') in
      let st = Seq.upd st (U16.v s) None in
      { tsm with model_store = st }

let model_bevict_from_store (tsm:thread_state_model)
                            (s:slot tsm.model_store_len)
  : tsm':thread_state_model{
        Seq.length tsm.model_store = Seq.length tsm'.model_store
    }
  = let open TSM in
    { tsm with model_store = Seq.upd tsm.model_store (U16.v s) None }

let timestamp_lt (t0 t1:T.timestamp) = t0 `U64.lt` t1

////////////////////////////////////////////////////////////////////////////////

let vget_model (tsm:thread_state_model) (s:slot tsm.model_store_len) (k:T.key) (v:T.data_value)
  : thread_state_model
  = match model_get_record tsm s with
    | None -> model_fail tsm
    | Some r ->
      if r.record_key <> k then model_fail tsm
      else if r.record_value <> T.V_dval v then model_fail tsm
      else tsm

let vput_model (tsm:thread_state_model) (s:slot tsm.model_store_len) (k:T.key) (v:T.data_value)
  : thread_state_model
  = match model_get_record tsm s with
    | None -> model_fail tsm
    | Some r ->
      if r.record_key <> k then model_fail tsm
      else if not (is_data_key k) then model_fail tsm
      else model_put_record tsm s ({r with record_value = T.V_dval v})

let vaddm_model (tsm:thread_state_model) (s:slot tsm.model_store_len) (r:T.record) (s':slot tsm.model_store_len)
  : thread_state_model
  = let k = r.T.record_key in
    let v = r.T.record_value in
    (* check store contains slot s' *)
    match model_get_record tsm s' with
    | None -> model_fail tsm
    | Some r' ->
      let k' = r'.record_key in
      let v' = r'.record_value in
      (* check k is a proper desc of k' *)
      if not (is_proper_descendent k k') then model_fail tsm
      (* check store does not contain slot s *)
      else if Some? (model_get_record tsm s) then model_fail tsm
      (* check type of v is consistent with k *)
      else if not (is_value_of k v) then model_fail tsm
      (* check v' is a merkle value *)
      else match to_merkle_value v' with
      | None -> model_fail tsm
      | Some v' ->
        let d = desc_dir k k' in
        let dh' = desc_hash_dir v' d in
        let h = hashfn v in
        match dh' with
        | T.Dh_vnone _ -> (* k' has no child in direction d *)
            (* first add must be init value *)
            if v <> init_value k then model_fail tsm
            else if points_to_some_slot tsm s' d then model_fail tsm
            else (
              let tsm = model_madd_to_store tsm s k v s' d in
              let v'_upd = update_merkle_value v' d k h false in
              model_update_value tsm s' (T.V_mval v'_upd)
            )

        | T.Dh_vsome {T.dhd_key=k2; T.dhd_h=h2; T.evicted_to_blum = b2} ->
          if k2 = k then (* k is a child of k' *)
            (* check hashes match and k was not evicted to blum *)
            if not (h2 = h && b2 = T.Vfalse) then model_fail tsm
            (* check slot s' does not contain a desc along direction d *)
            else if points_to_some_slot tsm s' d then model_fail tsm
            else model_madd_to_store tsm s k v s' d
          else
            (* first add must be init value *)
            if v <> init_value k then model_fail tsm
            (* check k2 is a proper desc of k *)
            else if not (is_proper_descendent k2 k) then model_fail tsm
            else
              let d2 = desc_dir k2 k in
              let Some mv = to_merkle_value v in
              let mv_upd = update_merkle_value mv d2 k2 h2 (b2=T.Vtrue) in
              let v'_upd = update_merkle_value v' d k h false in
              let tsm =
                  if points_to_some_slot tsm s' d then
                    model_madd_to_store_split tsm s k (T.V_mval mv_upd) s' d d2
                  else (
                    model_madd_to_store tsm s k (T.V_mval mv_upd) s' d
                  )
              in
              model_update_value tsm s' (T.V_mval v'_upd)


let vaddb_model (tsm:thread_state_model) (s:slot tsm.model_store_len) (r:T.record) (t:T.timestamp) (thread_id:T.thread_id)
  : thread_state_model
  = let { T.record_key = k;
          T.record_value = v } = r in
    (* check value type consistent with key k *)
    if not (is_value_of k v) then model_fail tsm
    else if Some? (model_get_record tsm s) then model_fail tsm
    else (
      //TODO: need to check that the key does not exist
      (* updated h_add *)
      let tsm = model_update_hadd tsm r t thread_id in
      (* updated clock *)
      let tsm = model_update_clock tsm t in
      (* add record to store *)
      model_put_record tsm s (mk_record k v T.BAdd)
    )

let vevictm_model (tsm:thread_state_model) (s s':slot tsm.model_store_len)
  : thread_state_model
  = if s = s' then model_fail tsm
    else (
      match model_get_record tsm s,
            model_get_record tsm s'
      with
      | Some r, Some r' ->
        let k = r.record_key in
        let v = r.record_value in
        let k' = r'.record_key in
        let v' = r'.record_value in
        (* check k is a proper descendent of k' *)
        if not (is_proper_descendent k k') then model_fail tsm
        (* check k does not have a (merkle) child in the store *)
        else if points_to_some_slot tsm s true
              || points_to_some_slot tsm s false
        then model_fail tsm
        else (
          let d = desc_dir k k' in
          let Some v' = to_merkle_value v' in
          let dh' = desc_hash_dir v' d in
          let h = hashfn v in
          match dh' with
          | T.Dh_vnone _ -> model_fail tsm
          | T.Dh_vsome {T.dhd_key=k2; T.dhd_h=h2; T.evicted_to_blum = b2} ->
            if k2 <> k then model_fail tsm
            else if Some? r.record_parent_slot &&
                    (fst (Some?.v r.record_parent_slot) <> s' ||
                     snd (Some?.v r.record_parent_slot) <> d)
            then model_fail tsm
            else if None? r.record_parent_slot
                 && points_to_some_slot tsm s' d
            then model_fail tsm
            else
              let v'_upd = update_merkle_value v' d k h false in
              let tsm = model_update_value tsm s' (T.V_mval v'_upd) in
              model_mevict_from_store tsm s s' d
        )
      | _ -> model_fail tsm
    )

let sat_evictb_checks (tsm:_)
                      (s:slot tsm.model_store_len)
                      (t:T.timestamp)
  : GTot bool
  = match model_get_record tsm s with
    | None -> false
    | Some r ->
      let k = r.record_key in
      let v = r.record_value in
      let clock = tsm.model_clock in
      (* check key at s is not root *)
      not (is_root k) &&

      (* check time of evict < current time *)
      clock `timestamp_lt` t &&

      (* check k has no (merkle) children n the store *)
      not (points_to_some_slot tsm s true) &&
      not (points_to_some_slot tsm s false)

let model_vevictb_update_hash_clock
       tsm
       (s:slot tsm.model_store_len)
       (t:T.timestamp { sat_evictb_checks tsm s t })
   : thread_state_model
   = let Some r = model_get_record tsm s in
     let k = r.record_key in
     let v = r.record_value in
     (* update evict hash *)
     let h = tsm.model_hevict in
     let h_upd = model_update_hash h ({T.record_key = k; T.record_value=v}) t tsm.model_thread_id in
     (* update hash *)
     { tsm with model_hevict = h_upd;
                model_clock = t }

let vevictb_model (tsm:thread_state_model) (s:slot tsm.model_store_len) (t:T.timestamp)
  : thread_state_model
  = if not (sat_evictb_checks tsm s t)
    then model_fail tsm
    else (
      let Some r = model_get_record tsm s in
      if r.record_add_method <> T.BAdd
      then model_fail tsm
      else (
        let tsm = model_vevictb_update_hash_clock tsm s t in
        model_bevict_from_store tsm s
      )
    )

let vevictbm_model (tsm:thread_state_model)
                   (s s':slot tsm.model_store_len)
                   (t:T.timestamp)
  : thread_state_model
  = if s = s' then model_fail tsm
    else if not (sat_evictb_checks tsm s t)
    then model_fail tsm
    else if None? (model_get_record tsm s')
    then model_fail tsm
    else (
      let Some r = model_get_record tsm s in
      let Some r' = model_get_record tsm s' in
      if r.record_add_method <> T.MAdd
      then model_fail tsm
      else (
        let k = r.record_key in
        let k' = r'.record_key in
        let v' = r'.record_value in
        if not (is_proper_descendent k k')
        then model_fail tsm
        else (
           let Some mv' = to_merkle_value v' in
           let d = desc_dir k k' in
           let dh' = desc_hash_dir mv' d in
           match dh' with
           | T.Dh_vnone _ -> model_fail tsm
           | T.Dh_vsome {T.dhd_key=k2; T.dhd_h=h2; T.evicted_to_blum = b2} ->
             if (k2 <> k) || (b2 = T.Vtrue)
             then model_fail tsm
             else if None? r.record_parent_slot
                  || fst (Some?.v r.record_parent_slot) <> s'
                  || snd (Some?.v r.record_parent_slot) <> d
             then model_fail tsm
             else (
               let tsm = model_vevictb_update_hash_clock tsm s t in
               let mv'_upd = update_merkle_value mv' d k h2 true in
               let tsm = model_update_value tsm s' (T.V_mval mv'_upd) in
               model_mevict_from_store tsm s s' d
           )
        )
      )
    )

let verify_step_model (tsm:thread_state_model) (e:T.vlog_entry) : thread_state_model =
  let open T in
  if tsm.model_failed then tsm
  else
    match e with
    | Ve_Get ve ->
      if U16.v ve.vegp_s < U16.v tsm.model_store_len
      then vget_model tsm ve.vegp_s ve.vegp_k ve.vegp_v
      else model_fail tsm
    | Ve_Put ve ->
      if U16.v ve.vegp_s < U16.v tsm.model_store_len
      then vput_model tsm ve.vegp_s ve.vegp_k ve.vegp_v
      else model_fail tsm 
    | Ve_AddM ve ->
      if U16.v ve.veam_s < U16.v tsm.model_store_len &&
         U16.v ve.veam_s2 < U16.v tsm.model_store_len
      then vaddm_model tsm ve.veam_s ve.veam_r ve.veam_s2
      else model_fail tsm
    | Ve_EvictM ve ->
      if U16.v ve.veem_s < U16.v tsm.model_store_len &&
         U16.v ve.veem_s2 < U16.v tsm.model_store_len
      then vevictm_model tsm ve.veem_s ve.veem_s2
      else model_fail tsm
    | Ve_AddB ve ->
      if U16.v ve.veab_s < U16.v tsm.model_store_len
      then vaddb_model tsm ve.veab_s ve.veab_r ve.veab_t ve.veab_j
      else model_fail tsm
    | Ve_EvictB ve ->
      if U16.v ve.veeb_s < U16.v tsm.model_store_len
      then vevictb_model tsm ve.veeb_s ve.veeb_t
      else model_fail tsm
    | Ve_EvictBM ve ->
      if U16.v ve.veebm_s < U16.v tsm.model_store_len &&
         U16.v ve.veebm_s2 < U16.v tsm.model_store_len
      then vevictbm_model tsm ve.veebm_s ve.veebm_s2 ve.veebm_t
      else model_fail tsm

let rec verify_model (tsm:thread_state_model) (s:Seq.seq T.vlog_entry)
  : Tot thread_state_model (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 
    || tsm.model_failed
    then tsm
    else let s_prefix = VSeq.prefix s (n - 1) in
         let tsm = verify_model tsm s_prefix in
         verify_step_model tsm (Seq.index s (n - 1))
