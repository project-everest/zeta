module Veritas.Steel.VerifierModel

open FStar.Ghost
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module MSH = Veritas.MultiSetHashDomain
module T = Veritas.Formats.Types

#set-options "--ide_id_info_off"

let data_key = T.key
let data_value = T.data_value
let thread_id = T.thread_id

let contents = Seq.seq (option T.record)
let model_hash = erased MSH.mset_ms_hashfn_dom

[@@erasable]
noeq
type thread_state_model = {
  model_failed : bool;
  model_store : contents;
  model_clock : erased U64.t;
  model_hadd : model_hash;
  model_hevict : model_hash;
}

let model_fail tsm = {tsm with model_failed=false}

let slot (tsm:thread_state_model) = i:T.slot_id{U16.v i < Seq.length tsm.model_store}

let model_get_record (tsm:thread_state_model) (s:slot tsm) : GTot (option T.record)
  = Seq.index tsm.model_store (U16.v s)

let model_put_record (tsm:thread_state_model) (s:slot tsm) (r:T.record)
  : thread_state_model
  = {tsm with model_store=Seq.upd tsm.model_store (U16.v s) (Some r)}

let model_evict_record (tsm:thread_state_model) (s:slot tsm)
  : thread_state_model
  = {tsm with model_store=Seq.upd tsm.model_store (U16.v s) None }

let vget_model (tsm:thread_state_model) (s:slot tsm) (v:T.value) : thread_state_model =
  match model_get_record tsm s with
  | None -> model_fail tsm
  | Some r ->
      if r.T.record_value <> v then model_fail tsm
      else tsm

let vput_model (tsm:thread_state_model) (s:slot tsm) (v:T.value) : thread_state_model
  = match model_get_record tsm s with
    | None -> model_fail tsm
    | Some r -> model_put_record tsm s ({r with T.record_value = v})

assume
val is_data_key (k:T.key) : bool

val is_value_of (k:T.key) (v:T.value) : bool
let is_value_of k v = if is_data_key k then T.V_dval? v else T.V_mval? v

let mk_record (k:T.key) (v:T.value{is_value_of k v}) (a:T.add_method) : T.record
  = {
      T.record_key = k;
      T.record_value = v;
      T.record_add_method = a;
      T.record_l_child_in_store = T.Vfalse;
      T.record_r_child_in_store = T.Vfalse
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

let timestamp_lt (t0 t1:T.timestamp) = t0 `U64.lt` t1

let vevictb_model (tsm:thread_state_model) (s:slot tsm) (t:T.timestamp) (thread_id:thread_id)
  : GTot thread_state_model
  = let clk = tsm.model_clock in
    if not (clk `timestamp_lt` t)
    then model_fail tsm
    else begin
      (* check that the vstore contains s *)
      match model_get_record tsm s with
      | None -> model_fail tsm
      | Some r ->
        (* update the evict hash *)
        let tsm = model_update_hevict tsm r t thread_id in
        (* advance clock to t *)
        let tsm = model_update_clock tsm t in
        (* evict record *)
        model_evict_record tsm s
    end

assume
val is_proper_descendent (k0 k1:T.key) : bool
assume
val has_instore_merkle_desc (tsm:thread_state_model) (s:slot tsm) : bool
assume
val desc_dir (k0:T.key) (k1:T.key { k0 `is_proper_descendent` k1 }) : bool
assume
val to_merkle_value (v:T.value) : option T.mval_value
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
  : (tsm':thread_state_model{Seq.length tsm.model_store = Seq.length tsm'.model_store})
assume
val model_madd_to_store_split (tsm:thread_state_model) (s:slot tsm) (k:T.key) (v:T.value) (s':slot tsm) (d d2:bool)
  : (tsm':thread_state_model{Seq.length tsm.model_store = Seq.length tsm'.model_store})


let vaddm_model (tsm:thread_state_model) (s:slot tsm) (r:T.record) (s':slot tsm) (thread_id:thread_id) : thread_state_model =
    let k = r.T.record_key in
    let v = r.T.record_value in
    (* check store contains slot s' *)
    match model_get_record tsm s' with
    | None -> model_fail tsm
    | Some r' ->
      let k' = r'.T.record_key in
      let v' = r'.T.record_value in
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
            else
              let tsm = model_put_record tsm s'
                ({r' with T.record_value=(T.V_mval (update_merkle_value v' d k h false))}) in
              let tsm = model_put_record tsm s (mk_record k v T.MAdd) in
              update_in_store tsm s' d true

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
              | None -> model_fail tsm
              | Some mv ->
                let mv_upd = update_merkle_value mv d2 k2 h2 (b2=T.Vtrue) in
                let v'_upd = update_merkle_value v' d k h false in
                let tsm =
                  if points_to_some_slot tsm s' d then
                    model_madd_to_store_split tsm s k v s' d d2
                  else (
                    model_madd_to_store tsm s k (T.V_mval mv_upd) s' d
                  )
                in
                model_put_record tsm s' ({r' with T.record_value=(T.V_mval v'_upd)})

let vevictbm_model (tsm:thread_state_model)
                   (s s':slot tsm)
                   (t:T.timestamp)
                   (thread_id:thread_id)
  : thread_state_model
  = match model_get_record tsm s, model_get_record tsm s' with
    | Some r, Some r' ->
      begin
      if not (is_proper_descendent r.T.record_key r'.T.record_key) then model_fail tsm
      else if has_instore_merkle_desc tsm s then model_fail tsm
      else if r.T.record_add_method <> T.MAdd then model_fail tsm
      else let d = desc_dir r.T.record_key r'.T.record_key in
           match to_merkle_value r'.T.record_value with
           | None -> model_fail tsm //should be impossible, since r' has a proper descendent
           | Some v' ->
             let dh' = desc_hash_dir v' d in
             match dh' with
             | T.Dh_vnone _ ->
               model_fail tsm
             | T.Dh_vsome {T.dhd_key=k2; T.dhd_h=h2; T.evicted_to_blum = b2} ->
               if (k2 <> r.T.record_key) `Prims.op_BarBar` (b2 = T.Vtrue)
               then model_fail tsm
               else let tsm = model_put_record tsm s' ({r' with T.record_value=(T.V_mval (update_merkle_value v' d r.T.record_key h2 true))}) in
                    let tsm = update_in_store tsm s' d false in
                    vevictb_model tsm s t thread_id
      end
    | _ -> model_fail tsm
