module Zeta.Steel.ThreadStateModel
(*
 * This module provides a logical specification for a single verifier
 * thread implemented in Steel
 **)

open FStar.Ghost
open Zeta.Steel.ApplicationTypes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Zeta.Steel.FormatsManual
open Zeta.Steel.LogEntry
module T = Zeta.Steel.FormatsManual
module P = Zeta.Steel.Parser
module L = FStar.List.Tot
module HA = Zeta.Steel.HashAccumulator
module C = FStar.Int.Cast
module KU = Zeta.Steel.KeyUtils
module A = Zeta.App
module SA = Zeta.SeqAux
open Zeta.Steel.Util
#push-options "--using_facts_from '* -FStar.Seq.Properties.slice_slice'"

type add_method =
  | MAdd
  | BAdd

[@@CAbstractStruct]
noeq
type store_entry = {
  key : key;
  value : (v:value { is_value_of key v });
  add_method : add_method;
  l_child_in_store : option slot;
  r_child_in_store : option slot;
  parent_slot : option (slot & bool);
}

let contents = Seq.lseq (option store_entry) (U16.v store_size)
let model_hash = HA.hash_value_t

let epoch_id = U32.t

[@@erasable]
noeq
type epoch_hash = {
  hadd: model_hash;
  hevict: model_hash;
}
let init_epoch_hash =  {
  hadd = HA.initial_hash;
  hevict = HA.initial_hash;
}
let epoch_hashes = m:Map.t epoch_id epoch_hash{ Map.domain m `Set.equal` Set.complement Set.empty }
let initial_epoch_hashes : epoch_hashes = Map.const init_epoch_hash
let app_results =
  Seq.seq (fid:A.appfn_id aprm &
           app_args fid &
           app_records fid &
           app_result fid)
           
[@@erasable]
noeq
type thread_state_model = {
  failed : bool;
  store : contents;
  clock : U64.t;
  epoch_hashes: epoch_hashes;
  thread_id: tid;
  processed_entries: Seq.seq log_entry;
  app_results: app_results;
  last_verified_epoch: option epoch_id
}

let fail tsm = {tsm with failed=true}

let get_entry (tsm:thread_state_model) (s:T.slot)
  : GTot (option store_entry)
  = Seq.index tsm.store (U16.v s)

let check_slot_bounds (s:T.slot_id)
  : bool
  = U16.lt s store_size
  
let has_slot (tsm:thread_state_model) (s:T.slot_id)
  = check_slot_bounds s &&
    Some? (get_entry tsm s)

let root_base_key: T.base_key = 
  let open T in
  { 
    k = { v3 = U64.zero; v2 = U64.zero ; v1 = U64.zero ; v0 = U64.zero };
    significant_digits = U16.zero;
  } 

let root_key: T.key = InternalKey root_base_key

let madd_to_store_root (tsm: thread_state_model) (s: T.slot) (v: T.value)
  : thread_state_model
  = if has_slot tsm s 
    || not (is_value_of root_key v)
    then tsm
    else
      let new_entry = {
        key = root_key;
        value = v;
        add_method = MAdd;
        l_child_in_store = None;
        r_child_in_store = None;
        parent_slot = None;
      } in
      let store' = Seq.upd tsm.store (U16.v s) (Some new_entry) in
      { tsm with store = store' }

let init_value (k:key)
  : T.value
  = if ApplicationKey? k
    then DValue None
    else MValue ({ l = Dh_vnone (); r = Dh_vnone ()})
  
let init_thread_state_model tid
  : thread_state_model
  = let tsm = {
      thread_id = tid;
      failed = false;
      store = Seq.create (U16.v store_size) None;
      clock = 0uL;
      epoch_hashes = initial_epoch_hashes;
      processed_entries = Seq.empty;
      app_results = Seq.empty;
      last_verified_epoch = None;
    } in
    if U16.v tid = 0 then 
      madd_to_store_root tsm U16.zero (init_value root_key)
    else tsm
  
let put_entry (tsm:thread_state_model) (s:T.slot) (r:store_entry)
  : thread_state_model
  = {tsm with store=Seq.upd tsm.store (U16.v s) (Some r)}

let key_of_slot (tsm:thread_state_model) (s:T.slot { has_slot tsm s })
  : GTot key
  = let Some v = get_entry tsm s in
    v.key

let update_value (tsm:thread_state_model)
                 (s:T.slot{has_slot tsm s})
                 (r:T.value {is_value_of (key_of_slot tsm s) r})
  : thread_state_model
  = let Some v = get_entry tsm s in
    put_entry tsm s ({v with value = r})

let evict_entry (tsm:thread_state_model) (s:T.slot)
  : thread_state_model
  = {tsm with store=Seq.upd tsm.store (U16.v s) None }

let mk_entry_full (k:key)
                  (v:T.value{is_value_of k v})
                  (a:add_method)
                  (l r:option T.slot)
                  (p:option (T.slot & bool))
  : store_entry
  = {
      key = k;
      value = v;
      add_method = a;
      l_child_in_store = l;
      r_child_in_store = r;
      parent_slot = p
    }

let mk_entry (k:key) (v:T.value{is_value_of k v}) (a:add_method) 
  : store_entry
  = mk_entry_full k v a None None None

let update_clock (tsm:thread_state_model) (ts:T.timestamp)
  : thread_state_model
  = { tsm with clock = ts }

let update_hash_value (ha:HA.hash_value_t)
                      (r:T.record)
                      (t:T.timestamp)
                      (tid:T.thread_id)
  : GTot HA.hash_value_t
  = let sr : T.stamped_record = { record = r; timestamp = t; thread_id = tid} in
    let b = spec_serializer_stamped_record sr in
    serialized_stamped_record_length sr;
    let h = HA.hash_one_value b in
    HA.aggregate_hashes ha h

let update_epoch_hadd (ehs:epoch_hashes)
                      (eid:epoch_id)
                      (r:T.record)
                      (t:T.timestamp)
                      (thread_id:T.thread_id)
  : GTot epoch_hashes
  = let eh = Map.sel ehs eid in
    let eh = { eh with hadd = update_hash_value eh.hadd r t thread_id } in
    Map.upd ehs eid eh

let update_epoch_hevict (ehs:epoch_hashes)
                        (eid:epoch_id)
                        (r:T.record)
                        (t:T.timestamp)
                        (thread_id:T.thread_id)
  : GTot epoch_hashes
  = let eh = Map.sel ehs eid in
    let eh = { eh with hevict = update_hash_value eh.hevict r t thread_id } in
    Map.upd ehs eid eh

let update_hadd (tsm:thread_state_model)
                (e:epoch_id)
                (r:T.record)
                (t:T.timestamp)
                (thread_id:T.thread_id)
  = {tsm with epoch_hashes = update_epoch_hadd tsm.epoch_hashes e r t thread_id }

let update_hevict (tsm:thread_state_model)
                  (e:epoch_id)
                  (r:T.record)
                  (t:T.timestamp)
                  (thread_id:T.thread_id)
  = {tsm with epoch_hashes = update_epoch_hevict tsm.epoch_hashes e r t thread_id }

let to_merkle_value (v:T.value)
  : option T.mval_value
  = match v with
    | T.MValue v -> Some v
    | _ -> None

let desc_hash_dir (v:T.mval_value) (d:bool)
  : T.descendent_hash
  = if d then v.T.l else v.T.r

let update_merkle_value (v:T.mval_value)
                        (d:bool)
                        (k:T.base_key)
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


let zero: T.hash_value =
  let open T in
  let z = U64.zero in
  { v3 = z; v2 = z; v1 = z ; v0 = z }

let points_to_some_slot (tsm:thread_state_model)
                        (s:T.slot)
                        (d:bool)
  : GTot bool
  = match get_entry tsm s with
    | None -> false
    | Some r ->
      if d
      then Some? (r.l_child_in_store)
      else Some? (r.r_child_in_store)

let madd_to_store (tsm:thread_state_model)
                  (s:T.slot)
                  (k:key)
                  (v:T.value)
                  (s':T.slot)
                  (d:bool)
  : tsm':thread_state_model{
        Seq.length tsm.store = Seq.length tsm'.store /\
        (forall (ss:T.slot). {:pattern has_slot tsm' ss}
          has_slot tsm ss ==>
          (has_slot tsm' ss /\
           ApplicationKey? (key_of_slot tsm ss) ==
           ApplicationKey? (key_of_slot tsm' ss)))
    }
  = if has_slot tsm s
    || not (is_value_of k v)
    || not (has_slot tsm s')
    then fail tsm
    else
      let Some r' = get_entry tsm s' in
      let new_entry = {
        key = k;
        value = v;
        add_method = MAdd;
        l_child_in_store = None;
        r_child_in_store = None;
        parent_slot = Some (s', d)
      } in
      let store' = Seq.upd tsm.store (U16.v s) (Some new_entry) in
      let r' =
        if d
        then { r' with l_child_in_store = Some s }
        else { r' with r_child_in_store = Some s }
      in
      let store'' = Seq.upd store' (U16.v s') (Some r') in
      {tsm with store = store''}

let update_parent_slot (r:store_entry) (s:(slot & bool))
  = { r with parent_slot = Some s }

let update_child (r:store_entry) (d:bool) (s:slot)
  : store_entry
  = if d then {r with l_child_in_store = Some s }
    else {r with r_child_in_store = Some s}

let child_slot (r:store_entry) (d:bool)
  : option slot
  = if d then r.l_child_in_store
    else r.r_child_in_store

let madd_to_store_split (tsm:thread_state_model)
                        (s:slot)
                        (k:key)
                        (v:T.value)
                        (s':slot)
                        (d d2:bool)
  : tsm':thread_state_model{
         Seq.length tsm.store = Seq.length tsm'.store /\
         (forall (ss:slot). {:pattern has_slot tsm' ss}
           (has_slot tsm ss ==>
             (has_slot tsm' ss /\
              ApplicationKey? (key_of_slot tsm ss) ==
              ApplicationKey? (key_of_slot tsm' ss))))}
  = let st = tsm.store in
    if has_slot tsm s
    || not (is_value_of k v)
    || not (has_slot tsm s')
    then fail tsm
    else
      match get_entry tsm s' with
      | Some r' ->
        let p = (s', d) in
        let s2_opt = child_slot r' d in
        match s2_opt with
        | None -> fail tsm
        | Some s2 ->
          if U16.v s2 >= Seq.length st
          then (assert false; fail tsm)
          else match Seq.index st (U16.v s2) with
               | None -> fail tsm
               | Some r2 ->
                 let e = mk_entry_full k v MAdd None None (Some p) in
                 let e = update_child e d2 s2 in
                 let e' = update_child r' d s in
                 let p2new = s, d2 in
                 let e2 = update_parent_slot r2 p2new in
                 let st = Seq.upd st (U16.v s) (Some e) in
                 let st = Seq.upd st (U16.v s') (Some e') in
                 let st = Seq.upd st (U16.v s2) (Some e2) in
                 { tsm with store = st }

let mevict_from_store (tsm:thread_state_model)
                      (s s':slot)
                      (d:bool)
  : tsm':thread_state_model{
        Seq.length tsm.store = Seq.length tsm'.store
    }
  = match get_entry tsm s' with
    | None -> tsm //fail
    | Some r' ->
      let e' =
        if d
        then { r' with l_child_in_store = None }
        else { r' with r_child_in_store = None }
      in
      let st = Seq.upd tsm.store (U16.v s') (Some e') in
      let st = Seq.upd st (U16.v s) None in
      { tsm with store = st }

let bevict_from_store (tsm:thread_state_model)
                      (s:slot)
  : tsm':thread_state_model{
        Seq.length tsm.store = Seq.length tsm'.store
    }
  = { tsm with store = Seq.upd tsm.store (U16.v s) None }

let timestamp_lt (t0 t1:T.timestamp) = t0 `U64.lt` t1

////////////////////////////////////////////////////////////////////////////////


let to_base_key (k:key)
  : GTot base_key
  = match k with
    | InternalKey k -> k
    | ApplicationKey k -> KU.lower_base_key (aprm.A.keyhashfn k)

let lower_base_key_sig_digits (k:key_type)
  : Lemma 
    (ensures (KU.lower_base_key (aprm.A.keyhashfn k)).significant_digits == 256us)
  = admit()

let key_with_descendent_is_merkle_key (k:key) (k':base_key)
  : Lemma 
    (requires k' `KU.is_proper_descendent` (to_base_key k))
    (ensures InternalKey? k)
    [SMTPat (k' `KU.is_proper_descendent` (to_base_key k))]
  = match k with
    | InternalKey _ -> ()
    | ApplicationKey k -> lower_base_key_sig_digits k
    
#push-options "--query_stats --z3rlimit_factor 2 --fuel 0 --ifuel 2"
let vaddm (tsm:thread_state_model)
          (s s': T.slot_id)
          (r: T.record)
  : GTot thread_state_model
  = if not (check_slot_bounds s)
     || not (check_slot_bounds s') 
   then fail tsm
   else (
    match r with
    | ( gk, gv ) ->
      begin
      (* check store contains slot s' *)
      match get_entry tsm s' with
      | None -> fail tsm
      | Some r' ->
        let k' = to_base_key r'.key in
        let v' = r'.value in
        let k = to_base_key gk in
        (* check k is a proper desc of k' *)
        if not (KU.is_proper_descendent k k') then fail tsm
        (* check store does not contain slot s *)
        else if Some? (get_entry tsm s) then fail tsm
        (* check v' is a merkle value *)
        else match to_merkle_value v' with
             | None -> fail tsm (* TODO: Remove this? we can assert(False) here *)
             | Some v' ->
               let d = KU.desc_dir k k' in
               let dh' = desc_hash_dir v' d in
               let h = HashValue.hashfn gv in
               match dh' with
               | T.Dh_vnone _ -> (* k' has no child in direction d *)
                 (* first add must be init value *)
                 if gv <> init_value gk then fail tsm
                 else if points_to_some_slot tsm s' d then fail tsm
                 else (
                   let tsm = madd_to_store tsm s gk gv s' d in
                   let v'_upd = update_merkle_value v' d k zero false in
                   update_value tsm s' (T.MValue v'_upd)
                 )
               | T.Dh_vsome {T.dhd_key=k2; T.dhd_h=h2; T.evicted_to_blum = b2} ->
                 if k2 = k then (* k is a child of k' *)
                 (* check hashes match and k was not evicted to blum *)
                 if not (h2 = h && b2 = T.Vfalse) then fail tsm
                 (* check slot s' does not contain a desc along direction d *)
                 else if points_to_some_slot tsm s' d then fail tsm
                      else madd_to_store tsm s gk gv s' d
                 else if gv <> init_value gk then fail tsm
                 (* check k2 is a proper desc of k *)
                 else if not (KU.is_proper_descendent k2 k) then fail tsm
                 else (
                   let d2 = KU.desc_dir k2 k in
                   let Some mv = to_merkle_value gv in
                   let mv_upd = update_merkle_value mv d2 k2 h2 (b2=T.Vtrue) in
                   let v'_upd = update_merkle_value v' d k zero false in
                   let tsm =
                       if points_to_some_slot tsm s' d then
                         madd_to_store_split tsm s gk (MValue mv_upd) s' d d2
                       else 
                         madd_to_store tsm s gk (MValue mv_upd) s' d
                   in
                   update_value tsm s' (MValue v'_upd)
                 )
        end
   )

let next (t:T.timestamp)
  : option T.timestamp
  = if FStar.UInt.fits (U64.v t + 1) 64
    then Some (U64.add t 1uL)
    else None

let max (t0 t1:T.timestamp) 
  : T.timestamp
  = if U64.(t0 <=^ t1) then t1 else t0

let epoch_of_timestamp (t:T.timestamp)
  : epoch_id
  = C.uint64_to_uint32 (t `U64.shift_right` 32ul)

let is_root_key (k:key) =
  match k with
  | InternalKey k -> k.significant_digits = 0us
  | _ -> false

let epoch_greater_than_last_verified_epoch 
       (lve:option epoch_id)
       (e:epoch_id)
  = match lve with
    | None -> true
    | Some e' -> U32.(e' <^ e)
    
let vaddb (tsm:thread_state_model)
          (s:slot_id)
          (t:T.timestamp)
          (thread_id:T.thread_id)          
          (r:T.record)
  : thread_state_model
  = if not (check_slot_bounds s) then fail tsm
    else match r with
    | ( k, v ) ->
      if is_root_key k then fail tsm //root key
      else if Some? (get_entry tsm s) then fail tsm //slot is already full
      else if not (epoch_greater_than_last_verified_epoch 
                          tsm.last_verified_epoch
                          (epoch_of_timestamp t))
      then fail tsm
      else (
        //add hash (k, v, t, thread_id) to hadd.[epoch_of_timestamp t]
        let tsm = update_hadd tsm (epoch_of_timestamp t) (k, v) t thread_id in
        match next t with //increment the time
        | None -> 
          fail tsm //overflow
        | Some t' -> 
          let tsm = update_clock tsm (max tsm.clock t') in
          put_entry tsm s (mk_entry k v BAdd)
      )

let vevictm (tsm:thread_state_model)
            (s s':slot_id)
  : thread_state_model
  = if not (check_slot_bounds s)
    || not (check_slot_bounds s') then fail tsm
    else if s = s' then fail tsm
    else (
      match get_entry tsm s,
            get_entry tsm s'
      with
      | None, _
      | _, None -> fail tsm
      | Some r, Some r' ->
        let gk = r.key in
        let v = r.value in
        let gk' = r'.key in
        let v' = r'.value in
        let k = to_base_key gk in
        let k' = to_base_key gk' in
        (* check k is a proper descendent of k' *)
        if not (KU.is_proper_descendent k k') then fail tsm
        (* check k does not have a (merkle) child in the store *)
        else if points_to_some_slot tsm s true
              || points_to_some_slot tsm s false
        then fail tsm
        else (
          let d = KU.desc_dir k k' in
          let Some v' = to_merkle_value v' in
          let dh' = desc_hash_dir v' d in
          let h = HashValue.hashfn v in
          match dh' with
          | T.Dh_vnone _ -> fail tsm
          | T.Dh_vsome {T.dhd_key=k2; T.dhd_h=h2; T.evicted_to_blum = b2} ->
            if k2 <> k then fail tsm
            else if Some? r.parent_slot &&
                    (fst (Some?.v r.parent_slot) <> s' ||
                     snd (Some?.v r.parent_slot) <> d)
            then fail tsm
            else if None? r.parent_slot
                 && points_to_some_slot tsm s' d
            then fail tsm
            else
              let v'_upd = update_merkle_value v' d k h false in
              let tsm = update_value tsm s' (T.MValue v'_upd) in
              mevict_from_store tsm s s' d
        )
      )

let sat_evictb_checks (tsm:_)
                      (s:slot)
                      (t:timestamp)
  : GTot bool
  = match get_entry tsm s with
    | None -> false
    | Some r ->
      let k = r.key in
      let v = r.value in
      let clock = tsm.clock in
      (* check key at s is not root *)
      not (is_root_key k) &&

      (* check time of evict < current time *)
      clock `timestamp_lt` t &&

      (* check k has no (merkle) children n the store *)
      not (points_to_some_slot tsm s true) &&
      not (points_to_some_slot tsm s false)

let vevictb_update_hash_clock (tsm:thread_state_model)
                              (s:slot)
                              (t:timestamp { sat_evictb_checks tsm s t })
   : thread_state_model
   = let Some r = get_entry tsm s in
     let k = r.key in
     let v = r.value in
     (* update evict hash *)
     let tsm = update_hevict tsm (epoch_of_timestamp t) (k, v) t tsm.thread_id in
     {tsm with clock = t}

let vevictb (tsm:thread_state_model)
            (s:slot_id)
            (t:timestamp)
  : thread_state_model
  = if not (check_slot_bounds s) then fail tsm
    else if not (sat_evictb_checks tsm s t)
    then fail tsm
    else (
      let Some r = get_entry tsm s in
      if r.add_method <> BAdd
      then fail tsm
      else (
        let tsm = vevictb_update_hash_clock tsm s t in
        bevict_from_store tsm s
      )
    )

let vevictbm (tsm:thread_state_model)
             (s s':slot_id)
             (t:timestamp)
  : thread_state_model
  = if not (check_slot_bounds s)
    || not (check_slot_bounds s') then fail tsm
    else if s = s' then fail tsm
    else if not (sat_evictb_checks tsm s t)
    then fail tsm
    else if None? (get_entry tsm s')
    then fail tsm
    else (
      let Some r = get_entry tsm s in
      let Some r' = get_entry tsm s' in
      if r.add_method <> MAdd
      then fail tsm
      else (
        let gk = r.key in
        let gk' = r'.key in
        let v' = r'.value in
        let k = to_base_key gk in
        let k' = to_base_key gk' in
        if not (KU.is_proper_descendent k k')
        then fail tsm
        else (
           let Some mv' = to_merkle_value v' in
           let d = KU.desc_dir k k' in
           let dh' = desc_hash_dir mv' d in
           match dh' with
           | T.Dh_vnone _ -> fail tsm
           | T.Dh_vsome {T.dhd_key=k2; T.dhd_h=h2; T.evicted_to_blum = b2} ->
             if (k2 <> k) || (b2 = T.Vtrue)
             then fail tsm
             else if None? r.parent_slot
                  || fst (Some?.v r.parent_slot) <> s'
                  || snd (Some?.v r.parent_slot) <> d
             then fail tsm
             else (
               let tsm = vevictb_update_hash_clock tsm s t in
               let mv'_upd = update_merkle_value mv' d k h2 true in
               let tsm = update_value tsm s' (MValue mv'_upd) in
               mevict_from_store tsm s s' d
           )
        )
      )
    )

let increment_epoch (t:timestamp)
  : option timestamp
  = let e = epoch_of_timestamp t in
    if not (FStar.UInt.fits (U32.v e + 1) 32)
    then None
    else
      let e' = U32.(e +^ 1ul) in
      Some (U64.shift_left (C.uint32_to_uint64 e') 32ul)
    
  
let nextepoch (tsm:thread_state_model)
  : thread_state_model

  = match increment_epoch tsm.clock with
    | None -> fail tsm //overflow
    | Some new_clock ->
      let new_epoch = epoch_of_timestamp new_clock in
      {tsm with clock=new_clock;
                epoch_hashes = Map.upd tsm.epoch_hashes new_epoch init_epoch_hash }

let maybe_increment_last_verified_epoch (e:option epoch_id)
  = match e with
    | None -> Some 0ul
    | Some e -> check_overflow_add32 e 1ul
    
    (*
=======
  = let e = epoch_of_timestamp tsm.clock in
    if not (FStar.UInt.fits (U32.v e + 1) 32)
    then fail tsm //overflow
    else (
      // increment epoch - we have already checked the result fits in 32 bits
      let e = U32.add e U32.one in
      let clock = U64.shift_left (C.uint32_to_uint64 e) 32ul in
      {tsm with clock=clock}
    )
>>>>>>> _arvind_zeta_generic
*)

let verifyepoch (tsm:thread_state_model)
  : thread_state_model
  = match maybe_increment_last_verified_epoch tsm.last_verified_epoch with
    | None -> fail tsm //overflow
    | Some e ->
      if epoch_of_timestamp tsm.clock = e
      then fail tsm //can't advance last_verified_epoch all the way up to the current clock
      else { tsm with last_verified_epoch = Some e }
    
let rec read_slots (tsm:thread_state_model)
                   (slots:Seq.seq slot_id)
  : GTot (option 
    (recs:Seq.seq (A.app_record aprm.A.adm){ 
      Seq.length recs == Seq.length slots /\
      (forall (s:slot_id). {:pattern Seq.contains slots s}
                    Seq.contains slots s ==> 
                    has_slot tsm s /\
                    ApplicationKey? (key_of_slot tsm s))
    })) (decreases (Seq.length slots))
  = if Seq.length slots = 0
    then (
      Seq.lemma_contains_empty #U16.t;
      assert (slots `Seq.equal` Seq.empty);
      Some Seq.empty
    )
    else (
      let hd = Seq.head slots in
      let tl = Seq.tail slots in
      assert (slots `Seq.equal` Seq.cons hd tl);
      Classical.forall_intro (Seq.contains_cons hd tl);
      match read_slots tsm (Seq.tail slots) with
      | None -> None
      | Some tl ->
        if U16.v hd >= U16.v store_size
        then None
        else match get_entry tsm hd with
             | None -> None //missing slot
             | Some r ->
               match r.key with
               | ApplicationKey k ->
                 let d = 
                     match r.value with
                     | DValue None -> A.Null
                     | DValue (Some d) -> A.DValue d
                 in
                 Some (Seq.Properties.cons (k, d) tl)
               | _ ->
                 None
    )

let check_distinct_keys (s:Seq.seq (A.app_record aprm.A.adm))
  : b:bool { b <==> A.distinct_keys s }
  = let open Zeta.SeqAux in
    let keys = map fst s in
    let b = distinct_elems_comp keys in
    assert (forall (i:seq_index keys). 
             Seq.index keys i ==
             fst (Seq.index s i));
    b

let rec write_slots (tsm:thread_state_model)
                    (slots:Seq.seq slot_id { forall (s:U16.t). {:pattern Seq.contains slots s}
                                                Seq.contains slots s ==> 
                                                has_slot tsm s /\
                                                ApplicationKey? (key_of_slot tsm s)
                                         })
                    (values:Seq.seq (A.app_value_nullable aprm.A.adm)
                      { Seq.length slots == Seq.length values })
  : GTot (tsm':thread_state_model{
            tsm.thread_id == tsm'.thread_id /\
            tsm.last_verified_epoch == tsm'.last_verified_epoch /\
            tsm.clock == tsm'.clock /\
            tsm.epoch_hashes == tsm'.epoch_hashes
         })
         (decreases Seq.length slots)
  = if Seq.length slots = 0
    then tsm
    else (
      let hd_slot = Seq.head slots in
      let tl = Seq.tail slots in
      assert (slots `Seq.equal` Seq.cons hd_slot tl);
      Classical.forall_intro (Seq.contains_cons hd_slot tl);
      let hd_value = 
        match Seq.head values with
        | A.Null -> DValue None
        | A.DValue d -> DValue (Some d)
      in
      let tsm = update_value tsm hd_slot hd_value in
      write_slots tsm (Seq.tail slots) (Seq.tail values)
    )
      
let runapp (tsm:thread_state_model)
           (pl:runApp_payload)
  : GTot (tsm':thread_state_model { 
            tsm'.thread_id == tsm.thread_id /\
            tsm'.last_verified_epoch == tsm.last_verified_epoch /\
            tsm'.clock == tsm.clock /\
            tsm'.epoch_hashes == tsm.epoch_hashes
         }) // Need the refinement for tsm_entries_invariant_verify_step
  = if not (Map.contains aprm.A.tbl pl.fid)
    then fail tsm //unknown fid
    else (
      match spec_app_parser pl.fid pl.rest.ebytes with
      | None -> fail tsm //parsing failed
      | Some ((arg, slots), len) -> 
        if len <> U32.v pl.rest.len
        then fail tsm //parsing failed, some bytes not consumed
        else if not (Zeta.SeqAux.distinct_elems_comp slots)
        then fail tsm //not distinct slots
        else
          let fsig = Map.sel aprm.A.tbl pl.fid in
          match read_slots tsm slots with
          | None -> fail tsm
          | Some recs ->
            if not (check_distinct_keys recs)
            then fail tsm
            else (
              let res = fsig.f arg recs in
              match res with
              | ( A.Fn_failure, _, _) -> fail tsm
              | (_, res, out_vals) ->
                let tsm = {tsm with app_results=Seq.Properties.snoc tsm.app_results (| pl.fid, arg, recs, res |)} in
                write_slots tsm slots out_vals
            )
        )

let verify_log_entry (tsm:thread_state_model)
                     (e:log_entry)
  : thread_state_model
  = let open T in
    match e with
    | AddM s s' r -> vaddm tsm s s' r
    | AddB s ts tid r -> vaddb tsm s ts tid r
    | EvictM p -> vevictm tsm p.s p.s_
    | EvictB p -> vevictb tsm p.s p.t
    | EvictBM p -> vevictbm tsm p.s p.s_ p.t
    | NextEpoch -> nextepoch tsm
    | VerifyEpoch -> verifyepoch tsm
    | RunApp p -> runapp tsm p

let verify_step_model (tsm:thread_state_model)
                      (e:log_entry)
  : thread_state_model
  = let open T in
    if tsm.failed then tsm
    else let tsm' = verify_log_entry tsm e in
         if VerifyEpoch? e && tsm'.failed
         then tsm' //verifyepoch failed, don't push a VerifyEpoch on the entries list
         else {tsm' with processed_entries = Seq.snoc tsm.processed_entries e }

let log = Seq.seq log_entry
let all_logs = Seq.lseq log (U32.v n_threads)

let rec verify_model (tsm:thread_state_model) (s:log)
  : Tot thread_state_model (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 
    || tsm.failed
    then tsm
    else let s_prefix = Zeta.SeqAux.prefix s (n - 1) in
         let tsm = verify_model tsm s_prefix in
         verify_step_model tsm (Seq.index s (n - 1))

let committed_log_entries (entries:Seq.seq log_entry)
  : GTot (Seq.seq log_entry)
  = let open Zeta.SeqAux in
    let is_verify_epoch = function VerifyEpoch -> true | _ -> false in
    if exists_sat_elems is_verify_epoch entries
    then let i = last_index is_verify_epoch entries in
         prefix entries (i + 1)
    else Seq.empty

let committed_entries (tsm:thread_state_model)
  : GTot (Seq.seq log_entry)
  = committed_log_entries tsm.processed_entries
  
let delta_app_results (tsm0 tsm1:thread_state_model)
  : GTot (Seq.seq app_results)
  = Prims.admit()

let bytes_of_app_results (s:Seq.seq app_results)
  : GTot bytes
  = Prims.admit()

let tsm_entries_invariant (tsm:thread_state_model) =
    not tsm.failed ==>
    tsm == verify_model (init_thread_state_model tsm.thread_id)
                        tsm.processed_entries

#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 8"
let tsm_entries_invariant_verify_step (tsm:thread_state_model)
                                      (le:log_entry)
  : Lemma 
    (requires tsm_entries_invariant tsm)
    (ensures tsm_entries_invariant (verify_step_model tsm le)  /\
             tsm.thread_id == (verify_step_model tsm le).thread_id
  )
  = if tsm.failed
    then ()
    else (
      let tsm_init = init_thread_state_model tsm.thread_id in
      let log0 = tsm.processed_entries in
      let tsm1 = verify_step_model tsm le in
      let log1 = (verify_step_model tsm le).processed_entries in
      if Seq.length log1 > Seq.length log0
      then assert (Zeta.SeqAux.prefix log1 (Seq.length log1 - 1) `Seq.equal` log0)
    )
#pop-options
  
let verify_step_last_verified_epoch_constant_ (tsm:thread_state_model) (le:log_entry)
  : Lemma
    (requires
      not (VerifyEpoch? le))
    (ensures (
      let tsm' = verify_step_model tsm le in
      tsm.last_verified_epoch == tsm'.last_verified_epoch))
  = ()

let uncommitted_entries (l:log)
  : GTot log
  = let n = Seq.length (committed_log_entries l) in
    Seq.slice l n (Seq.length l)


let committed_entries_idem (l:log)
  : Lemma 
    (requires
      Seq.length l == 0 \/
      VerifyEpoch? (Seq.index l (Seq.length l - 1)))
    (ensures
      committed_log_entries l `Seq.equal` l)
  = if Seq.length l = 0
    then ()
    else (
      let last = Seq.index l (Seq.length l - 1) in
      let is_verify = (function VerifyEpoch -> true | _ -> false) in
      Zeta.SeqAux.lemma_last_index_correct2
            is_verify
            l
            (Seq.length l - 1);
      Zeta.SeqAux.lemma_fullprefix_equal l
    )

let committed_entries_prefix (l:log)
  : Lemma 
    (requires
      Seq.length l > 0 /\
      not (VerifyEpoch? (Seq.index l (Seq.length l - 1))))
    (ensures
      committed_log_entries l `Seq.equal`
      committed_log_entries (Zeta.SeqAux.prefix l (Seq.length l - 1)))
  = let last = Seq.index l (Seq.length l - 1) in
    let is_verify = (function VerifyEpoch -> true | _ -> false) in
    Zeta.SeqAux.lemma_last_index_opt_last_elem_nsat
            is_verify
            l
  
#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 8"
let rec last_verified_epoch_constant_log (log:log) (tid:tid)
  : Lemma
    (ensures (
      let tsm1 = verify_model (init_thread_state_model tid) log in
      let tsm0 = verify_model (init_thread_state_model tid) (committed_log_entries log) in
      tsm1.last_verified_epoch == tsm0.last_verified_epoch))
    (decreases (Seq.length log))
  = if Seq.length log = 0
    then ()
    else (
      let prefix = Zeta.SeqAux.prefix log (Seq.length log - 1) in
      let last = Seq.index log (Seq.length log - 1) in
      match last with
      | VerifyEpoch ->
        committed_entries_idem log

      | _ -> 
        let tsm1 = verify_model (init_thread_state_model tid) log in
        let tsm1_prefix = verify_model (init_thread_state_model tid) prefix in
        assert (tsm1 == verify_step_model tsm1_prefix last);      
        last_verified_epoch_constant_log prefix tid;
        committed_entries_prefix log
    )
#pop-options

let last_verified_epoch_constant (tsm:thread_state_model)
  : Lemma
    (requires
      tsm_entries_invariant tsm /\
      not tsm.failed)
    (ensures (
      let tsm0 = verify_model (init_thread_state_model tsm.thread_id) (committed_entries tsm) in
      tsm.last_verified_epoch == tsm0.last_verified_epoch))
  = last_verified_epoch_constant_log tsm.processed_entries tsm.thread_id

#push-options "--fuel 1 --z3rlimit_factor 3"
let rec verify_model_thread_id_inv 
              (tsm:thread_state_model)
              (les:log)
  : Lemma (ensures (verify_model tsm les).thread_id == tsm.thread_id)
          (decreases (Seq.length les))
  = if Seq.length les = 0 then ()
    else verify_model_thread_id_inv tsm
         (Zeta.SeqAux.prefix les (Seq.length les - 1))
          
let verify_model_snoc (tsm:thread_state_model)
                      (les:log)
                      (le:log_entry)
  : Lemma (verify_step_model (verify_model tsm les) le ==
           verify_model tsm (Seq.snoc les le) /\
           tsm.thread_id == (verify_model tsm les).thread_id /\
           tsm.thread_id == (verify_model tsm (Seq.snoc les le)).thread_id)
          [SMTPat (verify_model tsm (Seq.snoc les le))]
  = assert (Zeta.SeqAux.prefix (Seq.snoc les le) (Seq.length les) `Seq.equal` les);
    assert ((verify_model tsm les).thread_id ==
            (verify_model tsm (Seq.snoc les le)).thread_id);
    verify_model_thread_id_inv tsm les;
    verify_model_thread_id_inv tsm (Seq.snoc les le)

let rec verify_model_log_append (tsm:thread_state_model)
                                (les les':log)
  : Lemma 
    (ensures
      verify_model tsm (Seq.append les les') ==
      verify_model (verify_model tsm les) les')
    (decreases (Seq.length les'))
  = if Seq.length les' = 0
    then assert (Seq.append les les' `Seq.equal` les)
    else (
      let prefix, last = Seq.un_snoc les' in
      verify_model_log_append tsm les prefix;
      verify_model_snoc tsm (Seq.append les prefix) last;
      Seq.append_assoc les prefix (Seq.create 1 last)
    )
           
#push-options "--z3rlimit_factor 2"
let rec verify_model_append
  (tsm:thread_state_model)
  (log:log)
  : Lemma
      (requires
        not tsm.failed /\
        not (verify_model tsm log).failed)
      (ensures
        (verify_model tsm log).processed_entries ==
        Seq.append tsm.processed_entries log)
      (decreases (Seq.length log))
  = if Seq.length log = 0
    then assert (Seq.append tsm.processed_entries log `Seq.equal` tsm.processed_entries)
    else (
      let prefix, last = Seq.un_snoc log in
      verify_model_append tsm prefix;
      assert (Seq.snoc (Seq.append tsm.processed_entries prefix) last `Seq.equal`
              Seq.append tsm.processed_entries log)
    )
#pop-options

#pop-options


let last_verified_epoch_clock_invariant (tsm:thread_state_model)
  : GTot bool
  = match tsm.last_verified_epoch with
    | None -> true
    | Some e -> U32.v e < U32.v (epoch_of_timestamp tsm.clock)

let epoch_ordering (t0 t1:timestamp)
  : Lemma
    (ensures U64.(t0 <=^ t1) ==>
             U32.(epoch_of_timestamp t0 <=^ epoch_of_timestamp t1))
  = admit()

let increment_epoch_increments (t:timestamp)
  : Lemma (match increment_epoch t with
           | None -> True
           | Some t' -> U32.v (epoch_of_timestamp t') = U32.v (epoch_of_timestamp t) + 1)
  = admit()
  
#push-options "--z3rlimit_factor 8"
let last_verified_epoch_clock_invariant_step
       (tsm:thread_state_model { last_verified_epoch_clock_invariant tsm })
       (le: log_entry)
  : Lemma 
    (let tsm' = verify_step_model tsm le in
     last_verified_epoch_clock_invariant tsm')
  = let tsm' = verify_step_model tsm le in
    if tsm'.failed
    then ()
    else 
      match le with
      | AddM _ _ _ -> ()
      | AddB _ ts _ _ ->
        let Some ts' = next ts in
        epoch_ordering tsm.clock (max tsm.clock ts')
      | EvictM _ -> ()
      | EvictB _
      | EvictBM _ ->
        epoch_ordering tsm.clock tsm'.clock
      | NextEpoch ->
        increment_epoch_increments tsm.clock
      | VerifyEpoch -> ()
      | RunApp _ -> ()

#push-options "--fuel 1"
let rec extend_step_invariant
           (tsm:thread_state_model)
           (les:log)
           (p: thread_state_model -> Type)
           (step_invariant: (tsm:thread_state_model { p tsm } -> le:log_entry -> Lemma (let tsm' = verify_step_model tsm le in p tsm')))
  : Lemma 
    (requires p tsm)
    (ensures  p (verify_model tsm les))
    (decreases (Seq.length les))
  = if Seq.length les = 0
    then ()
    else (
      let prefix = Zeta.SeqAux.prefix les (Seq.length les - 1) in
      let last = Seq.index les (Seq.length les - 1) in
      extend_step_invariant tsm prefix p step_invariant;
      let tsm = verify_model tsm prefix in
      step_invariant tsm last
    )
#pop-options

let last_verified_epoch_clock_invariant_steps
       (tsm:thread_state_model { tsm_entries_invariant tsm /\ not tsm.failed })
       (les: log)
  : Lemma 
    (let tsm' = verify_model tsm les in
     last_verified_epoch_clock_invariant tsm /\
     last_verified_epoch_clock_invariant tsm')
  = extend_step_invariant
        (init_thread_state_model tsm.thread_id)
        tsm.processed_entries
        (fun tsm -> last_verified_epoch_clock_invariant tsm)
        last_verified_epoch_clock_invariant_step;
    extend_step_invariant
           tsm
           les
           (fun tsm -> last_verified_epoch_clock_invariant tsm)
           last_verified_epoch_clock_invariant_step

#push-options "--fuel 1"
let tsm_entries_invariant_steps (tid:tid) (les:log)
  : Lemma (tsm_entries_invariant (verify_model (init_thread_state_model tid) les))
  = assert (tsm_entries_invariant (init_thread_state_model tid));
    extend_step_invariant (init_thread_state_model tid)
                          les
                          tsm_entries_invariant
                          (fun tsm le -> tsm_entries_invariant_verify_step tsm le)
#pop-options
  
let last_verified_epoch_monotonic (e0 e1:option epoch_id)
  = match e0, e1 with
    | None, _ -> true
    | Some e, None -> false
    | Some e0, Some e1 -> U32.(e0 <=^ e1) 
#restart-solver
let epoch_hashes_constant_step
       (tsm:thread_state_model { last_verified_epoch_clock_invariant tsm })
       (le: log_entry)
       (e: epoch_id {
         not (epoch_greater_than_last_verified_epoch tsm.last_verified_epoch e)
       })
 : Lemma 
   (let tsm' = verify_step_model tsm le in
    Map.sel tsm.epoch_hashes e == Map.sel tsm'.epoch_hashes e /\
    last_verified_epoch_monotonic tsm.last_verified_epoch tsm'.last_verified_epoch
    )
  = let tsm' = verify_step_model tsm le in
    if tsm'.failed
    then ()
    else match le with
         | AddB _ _ _ _ -> ()
         | EvictB _
         | EvictBM _ ->
           epoch_ordering tsm.clock tsm'.clock
         | NextEpoch ->
           increment_epoch_increments tsm.clock
         | _ -> ()

#push-options "--fuel 1"
let rec epoch_hashes_constant_steps
       (tsm:thread_state_model { tsm_entries_invariant tsm /\ last_verified_epoch_clock_invariant tsm })
       (les: log)
       (e: epoch_id {
         not (epoch_greater_than_last_verified_epoch tsm.last_verified_epoch e)
       })
 : Lemma
   (ensures (
     let tsm' = verify_model tsm les in
     Map.sel tsm.epoch_hashes e == Map.sel tsm'.epoch_hashes e /\
     last_verified_epoch_monotonic tsm.last_verified_epoch tsm'.last_verified_epoch))
   (decreases (Seq.length les))
 = if Seq.length les = 0
   || tsm.failed
   then ()
   else (
      let prefix = Zeta.SeqAux.prefix les (Seq.length les - 1) in
      let last = Seq.index les (Seq.length les - 1) in
      epoch_hashes_constant_steps tsm prefix e;
      last_verified_epoch_clock_invariant_steps tsm prefix;
      let tsm' = verify_model tsm prefix in
      epoch_hashes_constant_step tsm' last e
   )


let verified_epoch_hashes_constant (tsm:thread_state_model { tsm_entries_invariant tsm })
                                   (e:epoch_id {
                                     not (epoch_greater_than_last_verified_epoch tsm.last_verified_epoch e)
                                   })
                                   (les:log)
  : Lemma (let tsm' = verify_model tsm les in
           Map.sel tsm.epoch_hashes e == Map.sel tsm'.epoch_hashes e)
  = if tsm.failed
    then ()
    else (
        last_verified_epoch_clock_invariant_steps (init_thread_state_model tsm.thread_id) tsm.processed_entries;
        epoch_hashes_constant_steps tsm les e
    )

let delta_out_bytes (tsm tsm':thread_state_model)
  = bytes_of_app_results (delta_app_results tsm tsm')

let delta_out_bytes_idem (tsm:thread_state_model)
  : Lemma (delta_out_bytes tsm tsm == Seq.empty)
          [SMTPat (delta_out_bytes tsm tsm)]
  = admit()

let delta_out_bytes_not_runapp (tsm:thread_state_model)
                               (le:log_entry { not (RunApp? le) })
  : Lemma (delta_out_bytes tsm (verify_step_model tsm le) == Seq.empty)
          [SMTPat (delta_out_bytes tsm (verify_step_model tsm le))]
  = admit()

let delta_out_bytes_trans (tsm tsm1:thread_state_model)
                          (le:log_entry)
  : Lemma (ensures
              delta_out_bytes tsm (verify_step_model tsm1 le) ==
              Seq.append (delta_out_bytes tsm tsm1)
                         (delta_out_bytes tsm1 (verify_step_model tsm1 le)))
  = admit()

let run (tid:tid) = verify_model (init_thread_state_model tid)

let rec run_all (n:nat{n <= U32.v n_threads})
                (logs:Seq.lseq log n)
  : Seq.seq thread_state_model
  = if n = 0 then Seq.empty
    else let prefix, last = Seq.un_snoc logs in
         let tid_last = U16.uint_to_t (Seq.length logs - 1) in
         let tsms = run_all (n - 1) prefix in
         let tsm = run tid_last last in
         Seq.snoc tsms tsm
         
// let rec aggregate_epoch_hashes (tsms:Seq.seq thread_state_model) 
//                                (eid:epoch_id)
//   : GTot epoch_hash
//     (decreases Seq.length tsms)
//   = if Seq.length tsms = 0
//     then { init_epoch_hash }
//     else let hd = Seq.head tsms in
//          if hd.failed
//          then init_epoch_hash
//          else (
//            let tl_hash = aggregate_epoch_hashes (Seq.tail tsms) eid in
//            let hd_hash = Map.sel hd.epoch_hashes eid in
//            let hd_hash = 
//              if hd_hash.epoch_complete
//              then hd_hash
//              else init_epoch_hash
//            in
//            {
//              hadd   = HA.aggregate_hashes hd_hash.hadd tl_hash.hadd;
//              hevict = HA.aggregate_hashes hd_hash.hevict tl_hash.hevict;
//              epoch_complete = hd_hash.epoch_complete && tl_hash.epoch_complete
//            }
//          )

// let epoch_is_certified (logs:all_logs)
//                        (eid:epoch_id)
//   : GTot bool
//   = let tsms = run_all _ logs in
//     let aeh = aggregate_epoch_hashes tsms eid in
//     aeh.epoch_complete &&
//     aeh.hadd = aeh.hevict

