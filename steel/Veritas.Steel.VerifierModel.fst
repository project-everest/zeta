module Veritas.Steel.VerifierModel

open FStar.Ghost
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module MSH = Veritas.MultiSetHashDomain
module T = Veritas.Formats.Types


let data_key = k:T.key{ U16.v k.T.significant_digits = 256 }
let data_value = T.data_value
let thread_id = T.thread_id

type record = {
  record_key : T.key;
  record_value : T.value;
  record_add_method : T.add_method;
  record_l_child_in_store : option T.slot_id;
  record_r_child_in_store : option T.slot_id;
  record_parent_slot : option (T.slot_id & bool);
}

let contents = Seq.seq (option record)
let model_hash = MSH.ms_hash_value

[@@erasable]
noeq
type thread_state_model = {
  model_failed : bool;
  model_store : contents;
  model_clock : U64.t;
  model_hadd : model_hash;
  model_hevict : model_hash;
  model_thread_id: T.thread_id
}

let model_fail tsm = {tsm with model_failed=true}

let slot (tsm:thread_state_model) = i:T.slot_id{U16.v i < Seq.length tsm.model_store}

let model_get_record (tsm:thread_state_model) (s:slot tsm) : GTot (option record)
  = Seq.index tsm.model_store (U16.v s)
let has_slot (tsm:thread_state_model) (s:slot tsm) = Some? (model_get_record tsm s)

let model_put_record (tsm:thread_state_model) (s:slot tsm) (r:record)
  : thread_state_model
  = {tsm with model_store=Seq.upd tsm.model_store (U16.v s) (Some r)}

let model_update_value (tsm:thread_state_model)
                       (s:slot tsm{has_slot  tsm s})
                       (r:T.value)
  : thread_state_model
  = let Some v = model_get_record tsm s in
    model_put_record tsm s ({v with record_value = r})

let model_evict_record (tsm:thread_state_model) (s:slot tsm)
  : thread_state_model
  = {tsm with model_store=Seq.upd tsm.model_store (U16.v s) None }

assume
val is_data_key (k:T.key) : bool

assume
val is_root (k:T.key) : bool

val is_value_of (k:T.key) (v:T.value) : bool
let is_value_of k v = if is_data_key k then T.V_dval? v else T.V_mval? v

let mk_record (k:T.key) (v:T.value{is_value_of k v}) (a:T.add_method) : record
  = {
      record_key = k;
      record_value = v;
      record_add_method = a;
      record_l_child_in_store = None;
      record_r_child_in_store = None;
      record_parent_slot = None
    }

let model_update_clock (tsm:thread_state_model) (ts:T.timestamp)
  : thread_state_model
  = if FStar.UInt.fits (U64.v tsm.model_clock + U64.v ts) 64
    then { tsm with model_clock = tsm.model_clock `U64.add` ts } //+1
    else model_fail tsm

// AF: Should somewhat correspond to Veritas.MultiSetHash.ms_hashfn_upd
assume
val model_update_hash (h:model_hash) (r:T.record) (t:T.timestamp) (thread_id:thread_id)
  : model_hash

let model_update_hadd (tsm:_) (r:T.record) (t:T.timestamp) (thread_id:thread_id) =
  ({tsm with model_hadd = model_update_hash tsm.model_hadd r t thread_id})

let model_update_hevict (tsm:_) (r:T.record) (t:T.timestamp) (thread_id:thread_id) =
  ({tsm with model_hevict = model_update_hash tsm.model_hevict r t thread_id})


assume
val is_proper_descendent (k0 k1:T.key) : bool

assume
val has_instore_merkle_desc (tsm:thread_state_model) (s:slot tsm) : bool

assume
val desc_dir (k0:T.key) (k1:T.key { k0 `is_proper_descendent` k1 }) : bool

let to_merkle_value (v:T.value)
  : option T.mval_value
  = match v with
    | T.V_mval v -> Some v
    | _ -> None


assume
val desc_hash_dir (v:T.mval_value) (d:bool) : T.descendent_hash

assume
val update_merkle_value (v:T.mval_value) (d:bool) (k:T.key) (h:T.hash_value) (b:bool) : T.mval_value

assume
val update_in_store (tsm:thread_state_model) (s:slot tsm) (d:bool) (b:bool) : tsm':thread_state_model{Seq.length tsm.model_store = Seq.length tsm'.model_store}

assume
val hashfn (v:T.value) : T.hash_value

assume
val init_value (k:T.key) : T.value

assume
val points_to_some_slot (tsm:thread_state_model) (s:slot tsm) (d:bool) : bool

assume
val model_madd_to_store (tsm:thread_state_model) (s:slot tsm) (k:T.key) (v:T.value) (s':slot tsm) (d:bool)
  : (tsm':thread_state_model{
        Seq.length tsm.model_store = Seq.length tsm'.model_store /\
        (forall (ss:slot tsm). {:pattern has_slot tsm' ss} has_slot tsm ss ==> has_slot tsm' ss)
    })

assume
val model_madd_to_store_split (tsm:thread_state_model) (s:slot tsm) (k:T.key) (v:T.value) (s':slot tsm) (d d2:bool)
  : (tsm':thread_state_model{
         Seq.length tsm.model_store = Seq.length tsm'.model_store /\
         (forall (ss:slot tsm). {:pattern has_slot tsm' ss} has_slot tsm ss ==> has_slot tsm' ss)
    })


assume
val model_mevict_from_store (tsm:thread_state_model) (s s':slot tsm) (d:bool)
  : (tsm':thread_state_model{
        Seq.length tsm.model_store = Seq.length tsm'.model_store
    })

assume
val model_bevict_from_store (tsm:thread_state_model) (s:slot tsm)
  : (tsm':thread_state_model{
        Seq.length tsm.model_store = Seq.length tsm'.model_store
    })

let timestamp_lt (t0 t1:T.timestamp) = t0 `U64.lt` t1

////////////////////////////////////////////////////////////////////////////////

let vget_model (tsm:thread_state_model) (s:slot tsm) (k:data_key) (v:T.value) : thread_state_model =
  match model_get_record tsm s with
  | None -> model_fail tsm
  | Some r ->
      if r.record_key <> k then model_fail tsm
      else if r.record_value <> v then model_fail tsm
      else tsm

let vput_model (tsm:thread_state_model) (s:slot tsm) (k:data_key) (v:T.value) : thread_state_model
  = match model_get_record tsm s with
    | None -> model_fail tsm
    | Some r ->
      if r.record_key <> k then model_fail tsm
      else model_put_record tsm s ({r with record_value = v})

let vaddm_model (tsm:thread_state_model) (s:slot tsm) (r:T.record) (s':slot tsm) : thread_state_model =
    let k = r.T.record_key in
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
            else
              let tsm = model_madd_to_store tsm s k v s' d in
              let v'_upd = update_merkle_value v' d k h false in
              model_update_value tsm s' (T.V_mval v'_upd)

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
              match to_merkle_value v with
              | None -> model_fail tsm // NS: this case should be unnecessary because k has a proper descendent
              | Some mv ->
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


let vaddb_model (tsm:thread_state_model) (s:slot tsm) (r:T.record) (t:T.timestamp) (thread_id:thread_id)
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

let vevictm_model (tsm:thread_state_model) (s s':slot tsm)
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
          match to_merkle_value v' with
          | None -> model_fail tsm //TODO: should be impossible
          | Some v' ->
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
                      (s:slot tsm)
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
       (s:slot tsm)
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

let vevictb_model (tsm:thread_state_model) (s:slot tsm) (t:T.timestamp)
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
                   (s s':slot tsm)
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
           match to_merkle_value v' with
           | None -> model_fail tsm //should be impossible, since r' has a proper descendent
           | Some mv' ->
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
