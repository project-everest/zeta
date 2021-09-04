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
module PRF = Veritas.Steel.PRFSetHash

let counter_t = ref U64.t

noeq
type thread_state_t = {
  id           : T.thread_id;
  len          : U16.t;
  st           : vstore len;  //a map from keys (cache ids) to merkle leaf or internal nodes
  clock        : counter_t;
  hadd         : PRF.prf_set_hash; //current incremental set hash values; TODO
  hevict       : PRF.prf_set_hash;
  failed       : ref bool
}

[@@__reduce__; __steel_reduce__]
noextract
let thread_state_inv (t:thread_state_t) : vprop =
  is_vstore t.st `star`
  vptr t.clock `star`
  vptr t.failed `star`
  PRF.prf_set_hash_inv t.hadd `star`
  PRF.prf_set_hash_inv t.hevict

[@@ __steel_reduce__]
//unfold
let v_thread (#p:vprop) (t:thread_state_t)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (thread_state_inv t) /\ True)})
  : GTot thread_state_model
  = {
      model_thread_id = t.id;
      model_store_len = t.len;
      model_failed = sel t.failed (focus_rmem h (thread_state_inv t));
      model_store = asel t.st (focus_rmem h (thread_state_inv t));
      model_clock = sel t.clock (focus_rmem h (thread_state_inv t));
      model_hadd = PRF.v_hash t.hadd (focus_rmem h (thread_state_inv t));
      model_hevict = PRF.v_hash t.hevict (focus_rmem h (thread_state_inv t))
    }

let check_overflow_add (x y:U64.t)
  : res:option U64.t {
        if FStar.UInt.fits (U64.v x + U64.v y) 64
        then Some? res /\
             Some?.v res == U64.add x y
        else None? res
    }
 = let open U64 in
   let res = add_mod x y in
   if res <^ x then None
   else if res -^ x = y then Some res
   else None

val update_clock (ts:T.timestamp) (vs:thread_state_t)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> v_thread vs h1 == model_update_clock (v_thread vs h0) ts)

let update_clock (ts:T.timestamp) (vs:thread_state_t) =
  let c = Steel.Reference.read vs.clock in
  let res = check_overflow_add c ts in
  match res with
  | None ->
    write vs.failed true; ()
  | Some res ->
    write vs.clock res; ()

val points_to_some_slot (vs:_)
                        (s:slot vs.len)
                        (d:bool)

  : Steel bool
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> True)
    (ensures fun h0 b h1 ->
      b == VerifierModel.points_to_some_slot (v_thread vs h0) s d /\
      v_thread vs h0 == v_thread vs h1)
let points_to_some_slot vs s d
  = let r = vcache_get_record vs.st s in
    match r with
    | None -> false
    | Some r ->
      if d
      then Some? (r.record_l_child_in_store)
      else Some? (r.record_r_child_in_store)

val madd_to_store (vs:_)
                  (s:slot vs.len)
                  (k:T.key)
                  (v:T.value)
                  (s':slot vs.len)
                  (d:bool)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 ->
      not (has_slot (v_thread vs h0) s) /\
      is_value_of k v /\
      has_slot (v_thread vs h0) s')
    (ensures fun h0 _ h1 ->
      v_thread vs h1 == model_madd_to_store (v_thread vs h0) s k v s' d)

#push-options "--query_stats --fuel 0 --ifuel 1"
let madd_to_store vs s k v s' d
  = let h = get () in
    assert (not (has_slot (v_thread vs h) s)); //this one does too
    let r' = vcache_get_record vs.st s' in
    match r' with
    | Some r' ->
      let new_entry = {
        record_key = k;
        record_value = v;
        record_add_method = T.MAdd;
        record_l_child_in_store = None;
        record_r_child_in_store = None;
        record_parent_slot = Some (s', d)
      } in
      vcache_update_record vs.st s new_entry;
      let r' =
        if d
        then { r' with record_l_child_in_store = Some s }
        else { r' with record_r_child_in_store = Some s }
      in
      vcache_update_record vs.st s' r'

let coerce #a #p (x:a) (pf:squash (p x)) : x:a{p x} = x

val madd_to_store_split (vs:_)
                        (s:slot vs.len)
                        (k:T.key)
                        (v:T.value)
                        (s':slot vs.len)
                        (d d2:bool)

  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 ->
      not (has_slot (v_thread vs h0) s) /\
      is_value_of k v /\
      has_slot (v_thread vs h0) s')
    (ensures fun h0 _ h1 ->
      v_thread vs h1 == model_madd_to_store_split (v_thread vs h0) s k v s' d d2)

#push-options "--fuel 0 --ifuel 1"
let madd_to_store_split vs s k v s' d d2
  = let h = get () in
    assert (is_value_of k v);
    assert (not (has_slot (v_thread vs h) s)); //this one does too
    assert (has_slot (v_thread vs h) s');
    let r' = vcache_get_record vs.st s' in
    match r' with
    | Some r' ->
      let p = (s', d) in
      let s2_opt = record_child_slot r' d in
      match s2_opt with
      | None -> noop(); ()
      | Some s2 ->
        let r2 = vcache_get_record vs.st s2 in
        match r2 with
        | None -> noop() ; ()
        | Some r2 ->
          let pf : squash (is_value_of k v) = () in
          let v : (v:T.value { is_value_of k v }) =
              coerce v pf
          in
          let e = mk_record_full k v T.MAdd None None (Some p) in
          let e = record_update_child e d2 s2 in
          let e' = record_update_child r' d s in
          let p2new = s2, d2 in
          let e2 = record_update_parent_slot r2 p2new in
          vcache_update_record vs.st s e;
          vcache_update_record vs.st s' e';
          vcache_update_record vs.st s2 e2

val vevictb_update_hash_clock
       (vs:_)
       (s:slot vs.len)
       (t:T.timestamp)
   : Steel unit
     (thread_state_inv vs)
     (fun _ -> thread_state_inv vs)
     (requires fun h0 ->
       VerifierModel.sat_evictb_checks (v_thread vs h0) s t)
     (ensures fun h0 _ h1 ->
       VerifierModel.sat_evictb_checks (v_thread vs h0) s t /\
       v_thread vs h1 ==
       model_vevictb_update_hash_clock (v_thread vs h0) s t)
let vevictb_update_hash_clock vs s t
  = let h = get () in
    assert (VerifierModel.sat_evictb_checks (v_thread vs h) s t);
    let r = vcache_get_record vs.st s in
    let Some r = r in
    let record = { T.record_key = r.record_key;
                   T.record_value = r.record_value } in
    PRF.prf_update_hash vs.hevict record t vs.id;
    Steel.Reference.write vs.clock t

let bevict_from_store (vs:_) (s:slot vs.len)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 -> True)
    (ensures fun h0 _ h1 ->
       v_thread vs h1 ==
       model_bevict_from_store (v_thread vs h0) s)
  = vcache_evict_record vs.st s; ()

let update_value (vs:_) (s:slot vs.len) (v:T.value)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 ->
      has_slot (v_thread vs h0) s /\
      is_value_of (key_of_slot (v_thread vs h0) s) v)
    (ensures fun h0 _ h1 ->
      has_slot (v_thread vs h0) s /\
      is_value_of (key_of_slot (v_thread vs h0) s) v /\
      v_thread vs h1 == model_update_value (v_thread vs h0) s v)
  = let ropt = vcache_get_record vs.st s in //TODO: better to just update a field rather than read and write back a whole record
    let Some r = ropt in
    let r' = { r with record_value = v } in
    vcache_update_record vs.st s r'

let mevict_from_store (vs:_) (s s':slot vs.len) (d:_)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 -> True)
    (ensures fun h0 _ h1 ->
       v_thread vs h1 ==
       model_mevict_from_store (v_thread vs h0) s s' d)
  = let h = get () in
    let r' = vcache_get_record vs.st s' in
    match r' with
    | None ->
      noop();
      ()
    | Some r' ->
      if d
      then
        let e' = { r' with record_l_child_in_store = None } in
        vcache_update_record vs.st s' e';
        vcache_evict_record vs.st s;
        Steel.Effect.Atomic.return ()
      else
        let e' = { r' with record_r_child_in_store = None } in
        vcache_update_record vs.st s' e';
        vcache_evict_record vs.st s;
        Steel.Effect.Atomic.return ()

let fail (vs:thread_state_t) (msg:string)
  : SteelF unit
             (thread_state_inv vs)
             (fun _ -> thread_state_inv vs)
             (requires fun _ -> True)
             (ensures fun h0 _ h1 -> v_thread vs h1 == model_fail (v_thread vs h0))
  = write vs.failed true; ()

////////////////////////////////////////////////////////////////////////////////

val vget (vs: thread_state_t) (s:slot vs.len) (k:T.key) (v:T.data_value)
  : Steel unit
          (thread_state_inv vs)
          (fun _ -> thread_state_inv vs)
          (requires fun h -> True)
          (ensures fun h0 _ h1 ->
            v_thread vs h1 == vget_model (v_thread vs h0) s k v
          )

let vget (vs: thread_state_t) (s:slot vs.len) (k:T.key) (v:T.data_value)
  = let ro = VCache.vcache_get_record vs.st s in
    match ro with
    | None ->
      fail vs "Slot not found"
    | Some r' ->
      if k <> r'.record_key
      then (fail vs "Failed: inconsistent key in Get"; ())
      else if T.V_dval v <> r'.record_value
      then (fail vs "Failed: inconsistent value in Get"; ())
      // AF: Usual problem of Steel vs SteelF difference between the two branches
      else (noop (); ())

////////////////////////////////////////////////////////////////////////////////

val vput (vs: thread_state_t) (s:slot vs.len) (k:T.key) (v:T.data_value)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> True)
    (ensures fun h0 _ h1 ->
      v_thread vs h1 == vput_model (v_thread vs h0) s k v)

(* verifier write operation *)
let vput vs s k v
  = let ro = VCache.vcache_get_record vs.st s in
    match ro with
    | None ->
      fail vs "Slot not found"; ()

    | Some r ->
      if r.record_key <> k then (fail vs "slot-key mismatch"; ())
      else if not (is_data_key k) then (fail vs "not a data key"; ())
      else (
        vcache_update_record vs.st s ({ r with record_value = T.V_dval v });
        () //seem to need this
      )

////////////////////////////////////////////////////////////////////////////////

val vaddm (vs:_) (s:slot vs.len) (r:T.record) (s':slot vs.len)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 -> True)
    (ensures fun h0 _ h1 ->
      v_thread vs h1 == vaddm_model (v_thread vs h0) s r s')

let vaddm vs s r s'
  = let h = get () in
    assert (v_thread vs h == v_thread vs h); //necessary
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
             let h = hashfn v in //TODO: Need a better, low-level hash
             match dh' with
             | T.Dh_vnone _ -> (* k' has no child in direction d *)
             (* first add must be init value *)
               if v <> init_value k then fail vs "incorrect initial value"
               else (
                 let b = points_to_some_slot vs s' d in
                 if b then fail vs "points to some slot"
                 else (
                   let tsm = madd_to_store vs s k v s' d in
                   let v'_upd = update_merkle_value v' d k h false in
                   let s' : slot vs.len = s' in
                   update_value vs s' (T.V_mval v'_upd)
                 )
               )

             | T.Dh_vsome {T.dhd_key=k2; T.dhd_h=h2; T.evicted_to_blum = b2} ->
               if k2 = k then (* k is a child of k' *)
               (* check hashes match and k was not evicted to blum *)
               if not (h2 = h && b2 = T.Vfalse) then fail vs "hash mismatch or evicted"
               (* check slot s' does not contain a desc along direction d *)
               else (
                 let b = points_to_some_slot vs s' d in
                 if b then fail vs "points to some slot"
                 else madd_to_store vs s k v s' d
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
                  let b = points_to_some_slot vs s' d in
                  //can't share the continuation
                  if b
                  then (
                    madd_to_store_split vs s k (T.V_mval mv_upd) s' d d2;
                    update_value vs s' (T.V_mval v'_upd)
                  )
                  else (
                    madd_to_store vs s k (T.V_mval mv_upd) s' d;
                    update_value vs s' (T.V_mval v'_upd)
                  )
             )))
////////////////////////////////////////////////////////////////////////////////

val vevictm (vs:_) (s s':slot vs.len)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 -> True)
    (ensures fun h0 _ h1 ->
      v_thread vs h1 == vevictm_model (v_thread vs h0) s s')

let vevictm vs s s'
  = let h = get () in
    assert (v_thread vs h == v_thread vs h);  //this assert seems necessary
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
          let b1 = points_to_some_slot vs s true in
          let b2 = points_to_some_slot vs s false in
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
              else match r.record_parent_slot with
                   | None ->
                     let b = points_to_some_slot vs s' d in
                     if b then fail vs "parent slot mismatch"
                     else (
                       let h = hashfn v in //TODO: Lower
                       let v'_upd = update_merkle_value v' d k h false in
                       let tsm = update_value vs s' (T.V_mval v'_upd) in
                       mevict_from_store vs s s' d
                     )

                   | Some (p_s, p_d) ->
                     if p_s <> s' || p_d <> d
                     then fail vs "parent slot mismatch"
                     else (
                       let h = hashfn v in //TODO: Lower
                       let v'_upd = update_merkle_value v' d k h false in
                       let tsm = update_value vs s' (T.V_mval v'_upd) in
                       mevict_from_store vs s s' d
                     )
          ))

////////////////////////////////////////////////////////////////////////////////

val vaddb (vs:thread_state_t)
          (s:slot vs.len)
          (r:T.record)
          (t:T.timestamp)
          (thread_id:T.thread_id)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> True)
    (ensures fun h0 _ h1 ->
      v_thread vs h1 == vaddb_model (v_thread vs h0) s r t thread_id)

let vaddb vs s r t thread_id
  = let h = get() in
    assert (v_thread vs h == v_thread vs h);
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
        PRF.prf_update_hash vs.hadd r t thread_id;// vs;
        update_clock t vs;
        VCache.vcache_add_record vs.st s k v T.BAdd)
    )

////////////////////////////////////////////////////////////////////////////////

val sat_evictb_checks (vs:_)
                      (s:slot vs.len)
                      (t:T.timestamp)
  : Steel bool
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> True)
    (ensures fun h0 b h1 ->
      b == VerifierModel.sat_evictb_checks (v_thread vs h0) s t /\
      v_thread vs h0 == v_thread vs h1)
let sat_evictb_checks vs s t
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
        let b1 = points_to_some_slot vs s true in
        let b2 = points_to_some_slot vs s false in
        not b1 && not b2
      )

////////////////////////////////////////////////////////////////////////////////

val vevictb (vs:thread_state_t)
            (s:slot vs.len)
            (t:T.timestamp)

  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> True)
    (ensures  fun h0 _ h1 ->
      v_thread vs h1 == vevictb_model (v_thread vs h0) s t)

let vevictb vs s t
  = let chk = sat_evictb_checks vs s t in
    if not chk then fail vs "sat_evictb_checks failed"
    else (
      let Some r = VCache.vcache_get_record vs.st s in
      if r.record_add_method <> T.BAdd
      then fail vs "Record is not a BAdd"
      else (
        vevictb_update_hash_clock vs s t;
        bevict_from_store vs s
      )
    )

////////////////////////////////////////////////////////////////////////////////

val vevictbm (vs:_)
             (s s':slot vs.len)
             (t:T.timestamp)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (fun h0 -> True)
    (fun h0 _ h1 ->
      v_thread vs h1 == vevictbm_model (v_thread vs h0) s s' t)

let vevictbm vs s s' t
  = let h = get() in
    assert (v_thread vs h == v_thread vs h);
    if s = s' then fail vs "equal slots"
    else (
      let b = sat_evictb_checks vs s t in
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
                else match r.record_parent_slot with
                     | None -> fail vs "paren slot checks"
                     | Some (ps, pd) ->
                       if ps <> s' || pd <> d
                       then fail vs "paren slot checks"
                       else (
                         vevictb_update_hash_clock vs s t;
                         let mv'_upd = update_merkle_value mv' d k h2 true in
                         update_value vs s' (T.V_mval mv'_upd);
                         mevict_from_store vs s s' d
                       )
                )
            )
        )
      )
    )

////////////////////////////////////////////////////////////////////////////////

val verify_step (vs:_) (e:T.vlog_entry)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 ->
      not ((v_thread vs h0).model_failed))
    (ensures fun h0 _ h1 ->
      v_thread vs h1 == verify_step_model (v_thread vs h0) e)

let verify_step vs e
  = let h = get() in
    assert (not ((v_thread vs h).model_failed));
    let open U16 in
    let open T in
    match e with
    | Ve_Get ve ->
      if ve.vegp_s <^ vs.len
      then vget vs ve.vegp_s ve.vegp_k ve.vegp_v
      else fail vs "slot bounds check"
    | Ve_Put ve ->
      if ve.vegp_s <^ vs.len
      then vput vs ve.vegp_s ve.vegp_k ve.vegp_v
      else fail vs "slot bounds check"
    | Ve_AddM ve ->
      if ve.veam_s <^ vs.len &&
         ve.veam_s2 <^ vs.len
      then vaddm vs ve.veam_s ve.veam_r ve.veam_s2
      else fail vs "slot bounds check"
    | Ve_EvictM ve ->
      if ve.veem_s <^ vs.len &&
         ve.veem_s2 <^ vs.len
      then vevictm vs ve.veem_s ve.veem_s2
      else fail vs "slot bounds check"
    | Ve_AddB ve ->
      if ve.veab_s <^ vs.len
      then vaddb vs ve.veab_s ve.veab_r ve.veab_t ve.veab_j
      else fail vs "slot bounds check"
    | Ve_EvictB ve ->
      if ve.veeb_s <^ vs.len
      then vevictb vs ve.veeb_s ve.veeb_t
      else fail vs "slot bounds check"
    | Ve_EvictBM ve ->
      if ve.veebm_s <^ vs.len &&
         ve.veebm_s2 <^ vs.len
      then vevictbm vs ve.veebm_s ve.veebm_s2 ve.veebm_t
      else fail vs "slot bounds check"

////////////////////////////////////////////////////////////////////////////////

module L = Veritas.Steel.Log
module A = Steel.Array
module AT = Steel.Effect.Atomic
module U8 = FStar.UInt8

let log_append (l0 l1:L.repr) : L.repr = Seq.append l0 l1

let verify_log_post (s:L.repr) (l:L.log)
                    (tsm0: thread_state_model)
                    (sopt: option L.repr)
                    (tsm1: thread_state_model)
  = match sopt with
    | None ->
       tsm1.model_failed == true
    | Some s' ->
        // let a = L.log_array l in
        // L.parsed (A.asel a h1) (log_append s s') /\
       Log.parsed_log_inv l (log_append s s') /\
       tsm1 == verify_model tsm0 s'


let log_append_empty (s:L.repr)
  : Lemma
    (ensures
           log_append L.empty_log s == s /\
           log_append s L.empty_log == s)
    [SMTPatOr [[SMTPat (log_append L.empty_log s)];
               [SMTPat (log_append s L.empty_log)]]]
  = assert (Seq.equal (log_append L.empty_log s) s);
    assert (Seq.equal (log_append s L.empty_log) s)

let cons_log (e:T.vlog_entry) (s:L.repr) : L.repr = Seq.cons e s

let log_snoc_append (s:L.repr) (e:T.vlog_entry) (s':L.repr)
  : Lemma
    (ensures
           log_append (L.snoc_log s e) s' == log_append s (cons_log e s'))
    [SMTPat (log_append (L.snoc_log s e) s')]
  = assert (Seq.equal (Seq.append (Seq.snoc s e) s')
                      (Seq.append s (Seq.cons e s')))

#push-options "--fuel 1"
module VSeq = Veritas.SeqAux
let rec verify_model_cons (tsm:thread_state_model)
                          (e:T.vlog_entry)
                          (s:L.repr)
  : Lemma
    (ensures
      verify_model (verify_step_model tsm e) s ==
      verify_model tsm (cons_log e s))
    (decreases (Seq.length s))
    [SMTPat (verify_model (verify_step_model tsm e) s)]
  = let s = Ghost.reveal s in
    let s' = Seq.cons e s in
    let prefix = VSeq.prefix s' (Seq.length s' - 1) in
    let last = Seq.index s' (Seq.length s) in
    if tsm.model_failed
    then ()
    else (
      calc
      (==)
      {
        verify_model tsm s';
        (==) {}
        verify_step_model (verify_model tsm prefix) last;
      };
      if Seq.length prefix = 0
      then ()
      else (
        assert (prefix `Seq.equal`
                Seq.cons e (Seq.tail prefix));
        verify_model_cons tsm e (Seq.tail prefix);
        assert (verify_model tsm (Seq.cons e (Seq.tail prefix)) ==
                verify_model (verify_step_model tsm e) (Seq.tail prefix));
        calc
        (==)
        {
          verify_step_model (verify_model tsm prefix) last;
          (==) {}
          verify_step_model (verify_model (verify_step_model tsm e) (Seq.tail prefix)) last;
          (==) {  assert (Seq.tail prefix `Seq.equal` VSeq.prefix s (Seq.length s - 1)) }
          verify_model (verify_step_model tsm e) s;
        }
      )
    )

////////////////////////////////////////////////////////////////////////////////

val verify_log (#s:L.repr) (vs:_) (l:L.log)
  : Steel (option L.repr)
    (thread_state_inv vs `star` L.log_with_parsed_prefix l s)
    (fun o -> thread_state_inv vs `star` A.varray (L.log_array l))
    (requires fun _ -> True)
    (ensures fun h0 sopt h1 ->
      verify_log_post s l (v_thread vs h0) sopt (v_thread vs h1))

let rec verify_log #s vs l
  = let h0 = get () in
    assert (v_thread vs h0 == v_thread vs h0);
    let failed = read vs.failed in
    if failed
    then (
         L.dispose l;
         AT.return None
    )
    else (
      let r = L.read_next l in
      let h1 = get () in
      assert (v_thread vs h1 == v_thread vs h0);
      match r with
      | L.Finished ->
        assert (L.parsed_log_inv l (log_append s L.empty_log));
        change_equal_slprop (L.read_next_provides s l r)
                            (A.varray (L.log_array l));
        assert (verify_model (v_thread vs h0) L.empty_log ==
               v_thread vs h1);
        AT.return (Some L.empty_log)
      | L.Failed pos msg ->
        change_equal_slprop (L.read_next_provides s l r)
                            (A.varray (L.log_array l));
        write vs.failed true;
        AT.return None
      | L.Parsed_with_maybe_more entry ->
        verify_step vs entry;
        change_equal_slprop (L.read_next_provides s l r)
                            (L.log_with_parsed_prefix l (L.snoc_log s entry));
        let sopt = verify_log vs l in
        match sopt with
        | None ->
          AT.return None
        | Some s' ->
          AT.return (Some (cons_log entry s'))
    )
////////////////////////////////////////////////////////////////////////////////

let relate_log_to_array (l:L.log) tsm0 sopt tsm1
  : Lemma
    (requires verify_log_post L.empty_log l tsm0 sopt tsm1)
    (ensures verify_array_post (L.log_array l) tsm0 sopt tsm1)
  = assert (forall (s:L.repr). Seq.equal (log_append L.empty_log s) s); ()

let rewrite_log_array (a:A.array U8.t)
                      (l:L.log)
  : Steel unit
    (A.varray (L.log_array l))
    (fun _ -> A.varray a)
    (requires fun _ -> a == L.log_array l)
    (ensures fun _ _ _ -> True)
  = change_equal_slprop (A.varray (L.log_array l))
                        (A.varray a)
let verify_array vs len a =
  let h0 = get () in
  assert (v_thread vs h0 == v_thread vs h0);
  let l = L.initialize_log len a in
  let sopt = verify_log vs l in
  rewrite_log_array a l;
  let h2 = get () in
  relate_log_to_array l (v_thread vs h0) sopt (v_thread vs h2);
  AT.return sopt

let create tid store_size
  = let st = VCache.vcache_create store_size in
    let clock = Steel.Reference.malloc 0uL in
    let hadd = PRF.create () in
    let hevict = PRF.create () in
    let failed = Steel.Reference.malloc false in
    let vs = {
      id = tid;
      len = store_size;
      st = st;
      clock = clock;
      hadd = hadd;
      hevict = hevict;
      failed = failed
    } in
    AT.return vs

let free vs
  = Steel.Reference.free vs.clock;
    Steel.Reference.free vs.failed;
    VCache.free vs.st;
    PRF.free vs.hadd;
    PRF.free vs.hevict
