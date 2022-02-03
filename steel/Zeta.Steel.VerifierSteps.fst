module Zeta.Steel.VerifierSteps
friend Zeta.Steel.VerifierTypes
open Zeta.Steel.VerifierTypes
open FStar.Ghost
open Steel.ST.Util
module G = Steel.ST.GhostReference
module R = Steel.ST.Reference
module A = Steel.ST.Array
module TLM = Zeta.Steel.ThreadLogMap
open Zeta.Steel.ApplicationTypes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Zeta.Steel.FormatsManual
open Zeta.Steel.Util
module T = Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel
module AEH = Zeta.Steel.AggregateEpochHashes
module Cast = FStar.Int.Cast
open Zeta.Steel.EpochHashes
module KU = Zeta.Steel.KeyUtils
module EH = Zeta.Steel.EpochHashes
module HA = Zeta.Steel.HashAccumulator
#push-options "--ide_id_info_off"
#push-options "--query_stats --fuel 0 --ifuel 1"

let as_u32 (s:U16.t) : U32.t = Cast.uint16_to_uint32 s


let fail (#tsm:M.thread_state_model)
         (t:thread_state_t)
  : STT unit
    (thread_state_inv_core t tsm)
    (fun _ -> thread_state_inv_core t (M.fail tsm))
  = R.write t.failed true

let fail_as (#tsm:M.thread_state_model)
            (t:thread_state_t)
            (tsm':M.thread_state_model)
  : ST bool
    (thread_state_inv_core t tsm)
    (fun b -> thread_state_inv_core t (update_if b tsm tsm'))
    (requires tsm' == M.fail tsm)
    (ensures fun _ -> True)
  = R.write t.failed true;
    let b = true in
    intro_thread_state_inv_core (update_if b tsm tsm') t;
    return b


let extend_processed_entries #o
                             (#tsm:M.thread_state_model)
                             (t:thread_state_t)
                             (le:log_entry)
  : STGhost unit o
    (thread_state_inv_core t (M.verify_log_entry tsm le))
    (fun _ -> thread_state_inv t (M.verify_step_model tsm le))
    (requires
      not tsm.failed /\
      tsm_entries_invariant tsm /\
      t.thread_id == tsm.thread_id /\
      not (VerifyEpoch? le))
    (ensures fun _ -> True)
  = M.tsm_entries_invariant_verify_step tsm le;
    rewrite
        (thread_state_inv_core t _)
        (thread_state_inv_core t (M.verify_log_entry tsm le));
    G.write t.processed_entries (Seq.snoc tsm.processed_entries le);
    intro_thread_state_inv_core (M.verify_step_model tsm le) t;
    intro_thread_state_inv t

let maybe_extend_processed_entries #o
                                   (#tsm:M.thread_state_model)
                                   (t:thread_state_t)
                                   (b:bool)
                                   (le:log_entry)
  : STGhost unit o
    (thread_state_inv_core t (update_if b tsm (M.verify_log_entry tsm le)))
    (fun _ -> thread_state_inv t (update_if b tsm (M.verify_step_model tsm le)))
    (requires
      not tsm.failed /\
      tsm_entries_invariant tsm /\
      t.thread_id == tsm.thread_id /\
      not (VerifyEpoch? le))
    (ensures fun _ -> True)
  = if b
    then (
      rewrite
        (thread_state_inv_core t _)
        (thread_state_inv_core t (M.verify_log_entry tsm le));
      extend_processed_entries t le;
      rewrite
        (thread_state_inv t _)
        (thread_state_inv t (update_if b tsm (M.verify_step_model tsm le)))
    )
    else (
      rewrite (thread_state_inv_core t _)
              (thread_state_inv_core t (update_if b tsm (M.verify_step_model tsm le)));
      intro_thread_state_inv t
    )

////////////////////////////////////////////////////////////////////////////////
//create
////////////////////////////////////////////////////////////////////////////////

#push-options "--fuel 1"
let create (tid:tid)
  : STT thread_state_t
    emp
    (fun t -> thread_state_inv t (M.init_thread_state_model tid))
  = let failed = R.alloc false in
    let store : vstore = A.alloc None (as_u32 store_size) in
    let clock = R.alloc 0uL in
    let epoch_hashes = EpochMap.create 64ul M.init_epoch_hash in
    let last_verified_epoch = R.alloc 0ul in
    let processed_entries : G.ref (Seq.seq log_entry) = G.alloc Seq.empty in
    let app_results : G.ref M.app_results = G.alloc Seq.empty in
    let serialization_buffer = A.alloc 0uy 4096ul in
    let tsm = M.init_thread_state_model tid in
    let t : thread_state_t = {
        thread_id = tid;
        failed;
        store;
        clock;
        epoch_hashes;
        last_verified_epoch;
        processed_entries;
        app_results;
        serialization_buffer
    } in
    intro_exists _ (array_pts_to serialization_buffer);
    assert (tsm == M.verify_model tsm Seq.empty);
    intro_pure (tsm_entries_invariant (M.init_thread_state_model tid) /\
                t.thread_id == tsm.thread_id);
    rewrite (R.pts_to failed _ _ `star`
             array_pts_to store _ `star`
             R.pts_to clock _ _ `star`
             EpochMap.full_perm epoch_hashes _ _ `star`
             R.pts_to last_verified_epoch _ _ `star`
             G.pts_to processed_entries _ _ `star`
             G.pts_to app_results _ _ `star`
             exists_ (array_pts_to serialization_buffer) `star`
             pure (tsm_entries_invariant (M.init_thread_state_model tid) /\
                   t.thread_id == tsm.thread_id)
            )
            (thread_state_inv t (M.init_thread_state_model tid));
    return t
#pop-options

////////////////////////////////////////////////////////////////////////////////
//vaddm
////////////////////////////////////////////////////////////////////////////////

let madd_to_store_split (#tsm:M.thread_state_model)
                        (t:thread_state_t)
                        (s:T.slot)
                        (k:key)
                        (v:T.value)
                        (s':T.slot)
                        (d:bool)
                        (d2:bool)
  : STT unit
    (thread_state_inv_core t tsm)
    (fun _ -> thread_state_inv_core t (M.madd_to_store_split tsm s k v s' d d2))
  = let b = (T.is_value_of k v) in
    if not b
    then (fail t; return ())
    else (
      let ropt = A.read t.store (as_u32 s) in
      let ropt' = A.read t.store (as_u32 s') in
      match ropt with
      | Some _ -> fail t; return ()
      | _ ->
        match ropt' with
        | None -> fail t; return ()
        | Some r' ->
          let p = (s', d) in
          let s2_opt = M.child_slot r' d in
          match s2_opt with
          | None -> fail t; return ()
          | Some s2 ->
            let r2opt = A.read t.store (as_u32 s2) in
            match r2opt with
            | None -> fail t; return ()
            | Some r2 ->
              let e = M.mk_entry_full k v M.MAdd None None (Some p) in
              let e = M.update_child e d2 s2 in
              let e' = M.update_child r' d s in
              let p2new = s2, d2 in
              let e2 = M.update_parent_slot r2 p2new in
              A.write t.store (as_u32 s) (Some e);
              A.write t.store (as_u32 s') (Some e');
              A.write t.store (as_u32 s2) (Some e2);
              return ())

let madd_to_store (#tsm:M.thread_state_model)
                  (t:thread_state_t)
                  (s:T.slot)
                  (k:key)
                  (v:T.value)
                  (s':T.slot)
                  (d:bool)
  : STT unit
    (thread_state_inv_core t tsm)
    (fun _ -> thread_state_inv_core t (M.madd_to_store tsm s k v s' d))
  = let b = (T.is_value_of k v) in
    if not b
    then (fail t; return ())
    else (
      let ropt = A.read t.store (as_u32 s) in
      let ropt' = A.read t.store (as_u32 s') in
      match ropt with
      | Some _ -> fail t; return ()
      | _ ->
        match ropt' with
        | None -> fail t; return ()
        | Some r' ->
          let new_entry : M.store_entry = {
            key = k;
            value = v;
            add_method = M.MAdd;
            l_child_in_store = None;
            r_child_in_store = None;
            parent_slot = Some (s', d)
          } in
          A.write t.store (as_u32 s) (Some new_entry);
          let r' : M.store_entry =
            if d
            then { r' with l_child_in_store = Some s }
            else { r' with r_child_in_store = Some s }
          in
          A.write t.store (as_u32 s') (Some r');
          return ()
    )

let entry_points_to_some_slot (r:M.store_entry)
                              (d:bool)
  : bool
  = if d
    then Some? (r.l_child_in_store)
    else Some? (r.r_child_in_store)

let update_value (#tsm:M.thread_state_model)
                 (t:thread_state_t)
                 (s:slot { M.has_slot tsm s })
                 (r:value { T.is_value_of (M.key_of_slot tsm s) r})
  : STT unit
    (thread_state_inv_core t tsm)
    (fun _ -> thread_state_inv_core t (M.update_value tsm s r))
  = let Some v = A.read t.store (as_u32 s) in
    A.write t.store (as_u32 s) (Some ({v with M.value = r}));
    ()

let vaddm_core (#tsm:M.thread_state_model)
               (t:thread_state_t)
               (s s':slot_id)
               (r:T.record)
  : STT bool
    (thread_state_inv_core t tsm)
    (fun b -> thread_state_inv_core t (update_if b tsm (M.verify_log_entry tsm (AddM s s' r))))
  = let b = not (M.check_slot_bounds s)
          || not (M.check_slot_bounds s') in
    if b then (fail t; return true)
    else (
      let gk, gv = r in
      let ropt = A.read t.store (as_u32 s') in
      match ropt with
      | None -> (fail t; return true)
      | Some r' ->
        let k' = M.to_base_key r'.key in
        let v' = r'.value in
        let k = M.to_base_key gk in
        (* check k is a proper desc of k' *)
        if not (KU.is_proper_descendent k k')
        then (fail t; return true)
        (* check store does not contain slot s *)
        else (
          let sopt = A.read t.store (as_u32 s) in
          match sopt with
          | Some _ -> fail t; return true
          | _ ->
             match M.to_merkle_value v' with
             | None -> fail t; return true
             | Some v' ->
               let d = KU.desc_dir k k' in
               let dh' = M.desc_hash_dir v' d in
               let h = M.hashfn gv in //TODO: low-level hash
               match dh' returns
                     (STT bool
                          (thread_state_inv_core t tsm)
                          (fun b -> thread_state_inv_core t (update_if b tsm (M.vaddm tsm s s' r))))
               with
               | T.Dh_vnone _ -> (* k' has no child in direction d *)
                 (* first add must be init value *)
                 if gv <> M.init_value gk
                 then (let b = fail_as t _ in return b)
                 else if entry_points_to_some_slot r' d
                 then (let b = fail_as t _ in return b)
                 else (
                   madd_to_store t s gk gv s' d;
                   let v'_upd = M.update_merkle_value v' d k h false in
                   update_value t s' (T.MValue v'_upd);
                   return true
                 )
               | T.Dh_vsome {T.dhd_key=k2; T.dhd_h=h2; T.evicted_to_blum = b2} ->
                 if k2 = k
                 then (
                   if not (h2 = h && b2 = T.Vfalse)
                   then (let b = fail_as t _ in return b)
                   else if entry_points_to_some_slot r' d
                   then (let b = fail_as t _ in return b)
                   else (madd_to_store t s gk gv s' d;
                         assert_ (thread_state_inv_core t (M.vaddm tsm s s' r));
                         let b = true in
//                         intro_thread_state_inv_core (update_if b tsm (M.vaddm tsm s s' p)) t;
                         return b)
                 )
                 else if gv <> M.init_value gk
                 then (let b = fail_as t _ in return b)
                 (* check k2 is a proper desc of k *)
                 else if not (KU.is_proper_descendent k2 k)
                 then (let b = fail_as t _ in return b)
                 else (
                   let d2 = KU.desc_dir k2 k in
                   let Some mv = M.to_merkle_value gv in
                   let mv_upd = M.update_merkle_value mv d2 k2 h2 (b2=T.Vtrue) in
                   let v'_upd = M.update_merkle_value v' d k h false in
                   let b = entry_points_to_some_slot r' d in
                   if b returns
                     (STT bool
                          (thread_state_inv_core t tsm)
                          (fun b -> thread_state_inv_core t (update_if b tsm (M.vaddm tsm s s' r))))
                   then (
                     madd_to_store_split t s gk (MValue mv_upd) s' d d2;
                     update_value t s' (MValue v'_upd);
                     let b = true in
                     return b
                   )
                   else (
                     madd_to_store t s gk (MValue mv_upd) s' d;
                     update_value t s' (MValue v'_upd);
                     let b = true in
                     return b
                   )
                 )))

let vaddm (#tsm:M.thread_state_model)
          (t:thread_state_t)
          (s s':slot_id)
          (r:T.record)
  : ST bool
    (thread_state_inv t tsm)
    (fun b ->
      thread_state_inv t
           (update_if b tsm (M.verify_step_model tsm (AddM s s' r))))
    (requires not tsm.failed)
    (ensures fun _ -> True)
  = elim_thread_state_inv _;
    let b = vaddm_core t s s' r in
    maybe_extend_processed_entries t _ _;
    return b

////////////////////////////////////////////////////////////////////////////////
//vaddb
////////////////////////////////////////////////////////////////////////////////

let next (t:T.timestamp)
  : option T.timestamp
  = if FStar.UInt.fits (U64.v t + 1) 64
    then Some (U64.add t 1uL)
    else None

let max (t0 t1:T.timestamp)
  = let open U64 in
    if t0 >=^ t1 then t0 else t1

type htype =
  | HAdd
  | HEvict

let update_hash (c:M.epoch_hash)
                (r:T.record)
                (t:T.timestamp)
                (thread_id:T.thread_id)
                (ht:htype)
  : GTot M.epoch_hash
  = match ht with
    | HAdd -> { c with hadd = M.update_hash_value c.hadd r t thread_id }
    | HEvict -> { c with hevict = M.update_hash_value c.hevict r t thread_id }

let update_epoch_hash (tsm:M.thread_state_model)
                      (e:M.epoch_id)
                      (r:T.record)
                      (ts:T.timestamp)
                      (thread_id:T.thread_id)
                      (ht:htype)
   : M.thread_state_model
  = let c = Map.sel tsm.epoch_hashes e in
    {tsm with epoch_hashes =
                   Map.upd tsm.epoch_hashes
                      e
                      (update_hash c r ts thread_id ht)}

let maybe_update_epoch_hash (b:bool)
                            (tsm:M.thread_state_model)
                            (e:M.epoch_id)
                            (r:T.record)
                            (ts:T.timestamp)
                            (thread_id:T.thread_id)
                            (ht:htype)
   : M.thread_state_model
  = let c = Map.sel tsm.epoch_hashes e in
    {tsm with epoch_hashes =
                   Map.upd tsm.epoch_hashes
                      e
                      (update_if b c (update_hash c r ts thread_id ht))}

let maybe_update_epoch_hash_equiv
                          (b:bool)
                          (tsm:M.thread_state_model)
                          (e:M.epoch_id)
                          (r:T.record)
                          (ts:T.timestamp)
                          (thread_id:T.thread_id)
                          (ht:htype)
  : Lemma (requires
            Map.contains tsm.epoch_hashes e)
          (ensures
            maybe_update_epoch_hash b tsm e r ts thread_id ht ==
            update_if b tsm (update_epoch_hash tsm e r ts thread_id ht))
  = if b then ()
    else assert (Map.equal tsm.epoch_hashes (Map.upd tsm.epoch_hashes e (Map.sel tsm.epoch_hashes e)))

let unfold_epoch_hash_perm #o (k:M.epoch_id) (v:epoch_hashes_t) (c:M.epoch_hash)
  : STGhostT unit o
    (epoch_hash_perm k v c)
    (fun _ ->
      HA.ha_val v.hadd c.hadd `star`
      HA.ha_val v.hevict c.hevict)
  = rewrite (epoch_hash_perm k v c)
            (HA.ha_val v.hadd c.hadd `star`
             HA.ha_val v.hevict c.hevict)

let fold_epoch_hash_perm #o
                         (k:M.epoch_id)
                         (v:epoch_hashes_t)
                         (#had #hev:HA.hash_value_t)
                         (c:M.epoch_hash)
  : STGhost unit o
    (HA.ha_val v.hadd had `star`
     HA.ha_val v.hevict hev)
    (fun _ -> epoch_hash_perm k v c)
    (requires
      c.hadd == had /\
      c.hevict == hev)
    (ensures fun _ -> True)
  = rewrite (HA.ha_val v.hadd had `star`
             HA.ha_val v.hevict hev)
            (epoch_hash_perm k v c)


let ha_add (#v:erased (HA.hash_value_t))
           (ha:HA.ha)
           (l:U32.t)
           (#bs:erased bytes { U32.v l <= Seq.length bs /\ Seq.length bs <= HA.blake2_max_input_length })
           (input:A.array U8.t)
  : STT bool
       (HA.ha_val ha v `star` array_pts_to input bs)
       (fun b ->
         array_pts_to input bs `star`
         HA.ha_val ha (HA.maybe_aggregate_hashes b v
                         (HA.hash_one_value (Seq.slice bs 0 (U32.v l)))))
  = A.pts_to_length input _;
    let x = HA.add ha input l in
    return x

#push-options "--z3rlimit_factor 2"
let update_ht (#tsm:M.thread_state_model)
              (t:thread_state_t)
              (e:M.epoch_id)
              (r:T.record)
              (ts:T.timestamp)
              (thread_id:T.thread_id)
              (ht:htype)
  : STT bool
    (thread_state_inv_core t tsm)
    (fun b -> thread_state_inv_core t (update_if b tsm (update_epoch_hash tsm e r ts thread_id ht)))
  = let vopt = EpochMap.get t.epoch_hashes e in
    match vopt with
    | EpochMap.NotFound
    | EpochMap.Fresh ->
      rewrite (EpochMap.get_post _ _ _ _ _ vopt)
              (EpochMap.full_perm t.epoch_hashes M.init_epoch_hash tsm.epoch_hashes);
      return false

    | EpochMap.Found v ->
      rewrite (EpochMap.get_post _ _ _ _ _ vopt)
              (EpochMap.perm t.epoch_hashes M.init_epoch_hash tsm.epoch_hashes (PartialMap.upd EpochMap.empty_borrows e v) `star`
               EH.epoch_hash_perm e v (Map.sel tsm.epoch_hashes e));
      unfold_epoch_hash_perm _ _ _;
      let sr = {
        record = r;
        timestamp = ts;
        thread_id = thread_id
      } in
      T.serialized_stamped_record_length sr;
      let n = T.serialize_stamped_record 4096ul 0ul t.serialization_buffer sr in
      let bs = elim_exists () in
      elim_pure ( _ /\ _ /\ _ /\ _);
      let ha = if ht = HAdd then v.hadd else v.hevict in
      let b =
        match ht
              returns (STT bool
                           (HA.ha_val v.hadd (Map.sel tsm.epoch_hashes e).hadd `star`
                            HA.ha_val v.hevict (Map.sel tsm.epoch_hashes e).hevict `star`
                            array_pts_to t.serialization_buffer bs
                            )
                           (fun b ->
                             array_pts_to t.serialization_buffer bs `star`
                             EH.epoch_hash_perm e v
                              (update_if b (Map.sel tsm.epoch_hashes e)
                                           (update_hash (Map.sel tsm.epoch_hashes e) r ts thread_id ht))))
        with
        | HAdd ->
          let b = ha_add v.hadd n t.serialization_buffer in
          fold_epoch_hash_perm e v
               (update_if b (Map.sel tsm.epoch_hashes e)
                            (update_hash (Map.sel tsm.epoch_hashes e) r ts thread_id HAdd));
          return b
        | HEvict ->
          let b = ha_add v.hevict n t.serialization_buffer in
          fold_epoch_hash_perm e v
               (update_if b (Map.sel tsm.epoch_hashes e)
                            (update_hash (Map.sel tsm.epoch_hashes e) r ts thread_id HEvict));
          return b
      in
      EpochMap.ghost_put t.epoch_hashes e v _;
      rewrite (EpochMap.perm _ _ _ _)
              (EpochMap.full_perm t.epoch_hashes M.init_epoch_hash
                           (Map.upd tsm.epoch_hashes e
                                   (update_if b (Map.sel tsm.epoch_hashes e)
                                                (update_hash (Map.sel tsm.epoch_hashes e) r ts thread_id ht))));


      intro_exists _ (array_pts_to t.serialization_buffer);
      maybe_update_epoch_hash_equiv b tsm e r ts thread_id ht;
      rewrite (thread_state_inv_core t (maybe_update_epoch_hash b tsm e r ts thread_id ht))
              (thread_state_inv_core t (update_if b tsm (update_epoch_hash tsm e r ts thread_id ht)));
      return b
#pop-options

let vaddb_core (#tsm:M.thread_state_model)
          (t:thread_state_t)
          (s:slot_id)
          (ts:timestamp)
          (thread_id:T.thread_id)
          (r:T.record)
  : STT bool
       (thread_state_inv_core t tsm)
       (fun b -> thread_state_inv_core t (update_if b tsm (M.verify_log_entry tsm (AddB s ts thread_id r))))
  = let b = M.check_slot_bounds s in
    if not b then (fail t; return true)
    else (
      let (k, v) = r in
      if M.is_root_key k then (fail t; return true)
      else (
        let ropt = A.read t.store (as_u32 s) in
        if Some? ropt then (fail t; return true) //slot is already full
        else (
          //add hash (k, v, t, thread_id) to hadd.[epoch_of_timestamp t]
          let ok = update_ht t (M.epoch_of_timestamp ts) r ts thread_id HAdd in
          if ok
          then (
             rewrite (thread_state_inv_core t _)
                     (thread_state_inv_core t (update_epoch_hash tsm (M.epoch_of_timestamp ts) r ts thread_id HAdd));
            let ts_opt = next ts in
            match ts_opt with
            | None -> fail t; return true
            | Some t' ->
              let clock = R.read t.clock in
              let next_clock = max clock t' in
              R.write t.clock next_clock;
              A.write t.store (as_u32 s) (Some (M.mk_entry k v M.BAdd));
              return true
          )
          else (
            rewrite (thread_state_inv_core t _) (thread_state_inv_core t tsm);
            return ok
          )
        )
      )
    )

let vaddb (#tsm:M.thread_state_model)
          (t:thread_state_t)
          (s:slot_id)
          (ts:timestamp)
          (thread_id:T.thread_id)
          (r:T.record)
  = elim_thread_state_inv _;
    let b = vaddb_core t s ts thread_id r in
    maybe_extend_processed_entries t _ _;
    return b

////////////////////////////////////////////////////////////////////////////////
//vevictm
////////////////////////////////////////////////////////////////////////////////

let evict_from_store (#tsm:M.thread_state_model)
                     (t:thread_state_t)
                     (s:slot)
                     (s':slot { M.has_slot tsm s' })
                     (d:bool)
  : STT unit
    (thread_state_inv_core t tsm)
    (fun _ -> thread_state_inv_core t (M.mevict_from_store tsm s s' d))
  = let Some r' = A.read t.store (as_u32 s') in
    let e' =
        if d
        then { r' with M.l_child_in_store = None }
        else { r' with M.r_child_in_store = None }
    in
    A.write t.store (as_u32 s') (Some e');
    A.write t.store (as_u32 s) None;
    ()

let vevictm_core (#tsm:M.thread_state_model)
                 (t:thread_state_t)
                 (s s':slot_id)
  : STT unit
    (thread_state_inv_core t tsm)
    (fun _ -> thread_state_inv_core t (M.verify_log_entry tsm (EvictM ({s; s'}))))
  = if not (M.check_slot_bounds s)
    || not (M.check_slot_bounds s')
    then (R.write t.failed true; ())
    else if s = s'
    then (R.write t.failed true; ())
    else (
      let e = A.read t.store (as_u32 s) in
      let e' = A.read t.store (as_u32 s') in
      match e, e' with
      | None, _
      | _, None -> R.write t.failed true; ()
      | Some r, Some r' ->
        let gk = r.M.key in
        let v = r.M.value in
        let gk' = r'.M.key in
        let v' = r'.M.value in
        let k = M.to_base_key gk in
        let k' = M.to_base_key gk' in
        (* check k is a proper descendent of k' *)
        if not (KU.is_proper_descendent k k')
        then (R.write t.failed true; ())
        (* check k does not have a (merkle) child in the store *)
        else if entry_points_to_some_slot r true
             ||  entry_points_to_some_slot r false
        then (R.write t.failed true; ())
        else (
          let d = KU.desc_dir k k' in
          let Some v' = M.to_merkle_value v' in
          let dh' = M.desc_hash_dir v' d in
          let h = M.hashfn v in
          match dh' with
          | T.Dh_vnone _ -> fail t; ()
          | T.Dh_vsome {T.dhd_key=k2; T.dhd_h=h2; T.evicted_to_blum = b2} ->
            if k2 <> k then (fail t; ())
            else if Some? r.M.parent_slot &&
                    (fst (Some?.v r.M.parent_slot) <> s' ||
                     snd (Some?.v r.M.parent_slot) <> d)
            then (fail t; ())
            else if None? r.M.parent_slot
                 && entry_points_to_some_slot r' d
            then (fail t; ())
            else (
              let v'_upd = M.update_merkle_value v' d k h false in
              update_value t s' (T.MValue v'_upd);
              evict_from_store t s s' d;
              ()
            )
        )
      )

let vevictm (#tsm:M.thread_state_model)
            (t:thread_state_t)
            (s s':slot_id)
  = elim_thread_state_inv _;
    vevictm_core t s s';
    extend_processed_entries t _


////////////////////////////////////////////////////////////////////////////////
//vevictb
////////////////////////////////////////////////////////////////////////////////
let sat_evictb_checks (#tsm:M.thread_state_model)
                      (t:thread_state_t)
                      (s:slot)
                      (ts:timestamp)
  : ST bool
    (thread_state_inv_core t tsm)
    (fun _ -> thread_state_inv_core t tsm)
    (requires True)
    (ensures fun b -> b == M.sat_evictb_checks tsm s ts)
  = let ropt = A.read t.store (as_u32 s) in
    match ropt with
    | None ->
      return false
    | Some r ->
      let k = r.key in
      let v = r.value in
      let clock = R.read t.clock in
      let b =
        not (M.is_root_key k) &&
        (* check time of evict < current time *)
        clock `M.timestamp_lt` ts &&
        (* check k has no (merkle) children n the store *)
        not (entry_points_to_some_slot r true) &&
        not (entry_points_to_some_slot r false)
      in
      return b

let vevictb_update_hash_clock (#tsm:M.thread_state_model)
                              (t:thread_state_t)
                              (s:slot)
                              (ts:timestamp { M.sat_evictb_checks tsm s ts })
   : ST bool
     (thread_state_inv_core t tsm)
     (fun b -> thread_state_inv_core t (update_if b tsm (M.vevictb_update_hash_clock tsm s ts)))
     (requires tsm.thread_id == t.thread_id)
     (ensures fun _ -> True)
   = let Some r = A.read t.store (as_u32 s) in
     let k = r.key in
     let v = r.value in
     (* update evict hash *)
     let e = M.epoch_of_timestamp ts in
     let b = update_ht t e (k, v) ts t.thread_id HEvict in
     if b
     then (
       R.write t.clock ts;
       return b
     )
     else (
       rewrite (thread_state_inv_core t _) (thread_state_inv_core t tsm);
       return b
     )

let vevictb_core (#tsm:M.thread_state_model)
                 (t:thread_state_t)
                 (s:slot_id)
                 (ts:timestamp)
  : ST bool
    (thread_state_inv_core t tsm)
    (fun b -> thread_state_inv_core t (update_if b tsm (M.verify_log_entry tsm (EvictB ({s; t=ts})))))
    (requires t.thread_id == tsm.thread_id)
    (ensures fun _ -> True)
  = let bounds_failed = not (M.check_slot_bounds s) in
    if bounds_failed //not hoisting this leads to weirdness
    then (
      R.write t.failed true;
      return true
    )
    else (
      let b = sat_evictb_checks t s ts in
      if not b
      then (
        fail t;
        return true
      )
      else (
        let Some r = A.read t.store (as_u32 s) in
        if r.add_method <> M.BAdd
        then (fail t; return true)
        else (
          let b = vevictb_update_hash_clock t s ts in
          if b
          then (
            A.write t.store (as_u32 s) None;
            return true
          )
          else (
            rewrite (thread_state_inv_core t _)
                    (thread_state_inv_core t tsm);
            return false
          )
        )
      )
    )

let vevictb (#tsm:M.thread_state_model)
            (t:thread_state_t)
            (s:slot_id)
            (ts:timestamp)
  = elim_thread_state_inv _;
    let b = vevictb_core t s ts in
    maybe_extend_processed_entries t _ _;
    return b

////////////////////////////////////////////////////////////////////////////////
//vevictbm: A bit delicate. TODO should debug the SMT queries.
////////////////////////////////////////////////////////////////////////////////

let vevictbm_core (#tsm:M.thread_state_model)
                  (t:thread_state_t)
                  (s s':slot_id)
                  (ts:timestamp)
  : ST bool
    (thread_state_inv_core t tsm)
    (fun b -> thread_state_inv_core t (update_if b tsm (M.verify_log_entry tsm (EvictBM ({s; s'; t=ts})))))
    (t.thread_id == tsm.thread_id)
    (fun _ -> True)
  = let bounds_failed =
          not (M.check_slot_bounds s)
        || not (M.check_slot_bounds s')
    in
    if bounds_failed then fail_as t _
    else if s = s' then fail_as t _
    else let se_checks = sat_evictb_checks t s ts in
         if not se_checks then fail_as t _
         else let ropt = A.read t.store (as_u32 s') in
              match ropt with
              | None -> fail_as t _
              | Some r' ->
                let Some r = A.read t.store (as_u32 s) in
                if r.add_method <> M.MAdd
                then (let b = fail_as t _ in return b)
                else (
                  let gk = r.key in
                  let gk' = r'.key in
                  let v' = r'.value in
                  let k = M.to_base_key gk in
                  let k' = M.to_base_key gk' in
                  if not (KU.is_proper_descendent k k')
                  then let b = fail_as t _ in return b
                  else (
                    let Some mv' = M.to_merkle_value v' in
                    let d = KU.desc_dir k k' in
                    let dh' = M.desc_hash_dir mv' d in
                    match dh' returns
                          (STT bool (thread_state_inv_core t tsm)
                                    (fun b -> thread_state_inv_core t (update_if b tsm (M.vevictbm tsm s s' ts))))
                    with
                    | T.Dh_vnone _ ->
                      let b = fail_as t _ in return b

                    | T.Dh_vsome {T.dhd_key=k2;
                                  T.dhd_h=h2;
                                  T.evicted_to_blum = b2} ->
                      if (k2 <> k) || (b2 = T.Vtrue)
                      then let b = fail_as t _ in return b
                      else if None? r.parent_slot
                           || fst (Some?.v r.parent_slot) <> s'
                           || snd (Some?.v r.parent_slot) <> d
                      then let b = fail_as t _ in return b
                      else (
                        let b = vevictb_update_hash_clock t s ts in
                        if b
                        then (
                          // rewrite (thread_state_inv_core t _)
                          //         (thread_state_inv_core t (M.vevictb_update_hash_clock tsm s ts));
                          let mv'_upd = M.update_merkle_value mv' d k h2 true in
                          update_value t s' (MValue mv'_upd);
                          evict_from_store t s s' d;
                          return true
                        )
                        else (
                          rewrite (thread_state_inv_core t _)
                                  (thread_state_inv_core t tsm);
                          return false
                        ))))

let vevictbm (#tsm:M.thread_state_model)
             (t:thread_state_t)
             (s s':slot_id)
             (ts:timestamp)
  = elim_thread_state_inv _;
    let b = vevictbm_core t s s' ts in
    maybe_extend_processed_entries t b _;
    return b

////////////////////////////////////////////////////////////////////////////////
// nextepoch
////////////////////////////////////////////////////////////////////////////////

let new_epoch (e:M.epoch_id)
  : STT EH.epoch_hashes_t
    emp
    (fun v -> EH.epoch_hash_perm e v M.init_epoch_hash)
  = let hadd = HA.create () in
    let hev = HA.create () in
    let eh : EH.epoch_hashes_t = { hadd = hadd; hevict = hev } in
    rewrite (HA.ha_val hadd _ `star` HA.ha_val hev _)
            (EH.epoch_hash_perm e eh M.init_epoch_hash);
    return eh


let epoch_map_add (#v:Type0)
               (#contents:Type0)
               (#vp:M.epoch_id -> v -> contents -> vprop)
               (#init:Ghost.erased contents)
               (#m:Ghost.erased (EpochMap.repr contents))
               (a:EpochMap.tbl vp)
               (i:M.epoch_id)
               (x:v)
               (c:Ghost.erased contents)
  : STT unit
    (EpochMap.full_perm a init m `star`
     vp i x c)
    (fun _ ->
      EpochMap.full_perm a init (Map.upd m i c))
  = EpochMap.put a i x _;
    assert (PartialMap.remove (EpochMap.empty_borrows #v) i `PartialMap.equal`
            EpochMap.empty_borrows #v);
    rewrite (EpochMap.perm a _ _ (PartialMap.remove EpochMap.empty_borrows i))
            (EpochMap.full_perm a init (Map.upd m i c))

let nextepoch_core (#tsm:M.thread_state_model)
                   (t:thread_state_t)
  : STT unit
    (thread_state_inv_core t tsm)
    (fun _ -> thread_state_inv_core t (M.verify_log_entry tsm NextEpoch))
  = let c = R.read t.clock in
    let e = M.epoch_of_timestamp c in
    let res = st_check_overflow_add32 e 1ul in //Ugh. need this wrapper, else weirdness
    match res with
    | None ->
      fail t; ()
    | Some nxt ->
      let c = U64.shift_left (Cast.uint32_to_uint64 nxt) 32ul in
      R.write t.clock c;
      let eht = new_epoch nxt in
      epoch_map_add t.epoch_hashes nxt eht M.init_epoch_hash;
      ()

let nextepoch (#tsm:M.thread_state_model)
              (t:thread_state_t)
  = elim_thread_state_inv _;
    nextepoch_core t;
    extend_processed_entries t _

////////////////////////////////////////////////////////////////////////////////
//verify_epoch: One of the most delicate functions in the API is
//verify_epoch, since it involves working with the aggregate epoch state
////////////////////////////////////////////////////////////////////////////////
let spec_verify_epoch (tsm:M.thread_state_model)
  = M.verify_step_model tsm VerifyEpoch

let aggregate_one_epoch_hash (source:AEH.epoch_hashes_repr)
                             (dest:AEH.epoch_hashes_repr)
                             (e:M.epoch_id)
  : AEH.epoch_hashes_repr
  = Map.upd dest e (AEH.aggregate_epoch_hash
                      (Map.sel dest e)
                      (Map.sel source e))

let aggregate_epoch_hash (b0 b1:bool) (e0 e1:M.epoch_hash)
  : M.epoch_hash
  = { hadd = update_if b0 e0.hadd (HA.aggregate_hashes e0.hadd e1.hadd);
      hevict = update_if b1 e0.hevict (HA.aggregate_hashes e0.hevict e1.hevict) }


let aggregate_epoch_hashes_t (#e:_)
                             (#s #d:M.epoch_hash)
                             (src:EH.epoch_hashes_t)
                             (dst:EH.epoch_hashes_t)
  : STT bool
    (EH.epoch_hash_perm e src s `star`
     EH.epoch_hash_perm e dst d)
    (fun b ->
      EH.epoch_hash_perm e src s `star`
      (if b
       then EH.epoch_hash_perm e dst (AEH.aggregate_epoch_hash d s)
       else exists_ (EH.epoch_hash_perm e dst)))
  = unfold_epoch_hash_perm e src s;
    unfold_epoch_hash_perm e dst d;
    let b = HA.aggregate dst.hadd src.hadd in
    if b
    then (
      rewrite (HA.ha_val dst.hadd _)
              (HA.ha_val dst.hadd (AEH.aggregate_epoch_hash d s).M.hadd);
      let b = HA.aggregate dst.hevict src.hevict in
      fold_epoch_hash_perm e src s;
      if b
      then (
        rewrite (HA.ha_val dst.hevict _)
                (HA.ha_val dst.hevict (AEH.aggregate_epoch_hash d s).M.hevict);
        fold_epoch_hash_perm e dst (update_if true d (AEH.aggregate_epoch_hash d s));
        return true
      )
      else (
        let w : M.epoch_hash =
          { hadd = (AEH.aggregate_epoch_hash d s).M.hadd;
            hevict = d.hevict }
        in
        rewrite (HA.ha_val dst.hadd _)
                (HA.ha_val dst.hadd w.hadd);
        rewrite (HA.ha_val dst.hevict _)
                (HA.ha_val dst.hevict w.hevict);
        fold_epoch_hash_perm e dst w;
        intro_exists w (EH.epoch_hash_perm e dst);
        return false
      )
    )
    else (
      fold_epoch_hash_perm e src s;
      rewrite (HA.ha_val dst.hadd _)
              (HA.ha_val dst.hadd d.hadd);
      fold_epoch_hash_perm e dst d;
      intro_exists d (EH.epoch_hash_perm e dst);
      return false
    )

inline_for_extraction
let with_value_of_key (#v:Type0)
                      (#contents:Type0)
                      (#vp: M.epoch_id -> v -> contents -> vprop)
                      (#init: erased contents)
                      (#m:erased (EpochMap.repr contents))
                      (#cf:contents -> GTot contents)
                      (t:EpochMap.tbl vp)
                      (i:M.epoch_id)
                      ($f: (value:v -> STT unit
                                         (vp i value (Map.sel m i))
                                         (fun _ -> vp i value (cf (Map.sel m i)))))
  : STT bool
    (EpochMap.full_perm t init m)
    (fun b -> EpochMap.full_perm t init (update_if b (reveal m) (Map.upd m i (cf (Map.sel m i)))))
  = let res = EpochMap.get t i in
    match res with
    | EpochMap.Found value ->
      rewrite (EpochMap.get_post _ _ _ _ _ _)
              (EpochMap.perm t init m (PartialMap.upd EpochMap.empty_borrows i value) `star`
               vp i value (Map.sel m i));
      f value;
      EpochMap.ghost_put t i value _;
      return true
    | _ ->
      rewrite (EpochMap.get_post _ _ _ _ _ _)
              (EpochMap.full_perm t init m);
      return false

/// Updates the aggregate epoch hash for a thread with the
/// t thread-local epoch hashes for epoch e
let rec propagate_epoch_hash (#tsm:M.thread_state_model)
                             (t:thread_state_t)
                             (#hv:erased AEH.epoch_hashes_repr)
                             (hashes : AEH.all_epoch_hashes)
                             (e:M.epoch_id)
  : STT bool
    (thread_state_inv_core t tsm `star`
     EpochMap.full_perm hashes M.init_epoch_hash hv)
    (fun b ->
      thread_state_inv_core t tsm `star`
      (if b
       then EpochMap.full_perm hashes M.init_epoch_hash (aggregate_one_epoch_hash (spec_verify_epoch tsm).epoch_hashes hv e)
       else exists_ (EpochMap.full_perm hashes M.init_epoch_hash)))
  = let dst = EpochMap.get hashes e in
    match dst with
    | EpochMap.NotFound ->
      rewrite (EpochMap.get_post _ _ _ _ _ _)
              (EpochMap.full_perm hashes M.init_epoch_hash hv);
      intro_exists_erased hv (EpochMap.full_perm hashes M.init_epoch_hash);
      return false

    | EpochMap.Fresh ->
      rewrite (EpochMap.get_post _ _ _ _ _ _)
              (EpochMap.full_perm hashes M.init_epoch_hash hv);
      let eh = new_epoch e in
      epoch_map_add hashes e eh _;
      let b = propagate_epoch_hash t hashes e in
      if b then (
        rewrite (if b then _ else _)
                (EpochMap.full_perm hashes M.init_epoch_hash
                                    (aggregate_one_epoch_hash (spec_verify_epoch tsm).epoch_hashes
                                                              (Map.upd hv e M.init_epoch_hash)
                                                              e));
        assert (Map.sel hv e == M.init_epoch_hash);
        assert (Map.upd hv e M.init_epoch_hash `Map.equal` reveal hv);
        rewrite (EpochMap.full_perm hashes M.init_epoch_hash
                                    (aggregate_one_epoch_hash (spec_verify_epoch tsm).epoch_hashes
                                                              (Map.upd hv e M.init_epoch_hash)
                                                              e))
                (EpochMap.full_perm hashes M.init_epoch_hash
                                    (aggregate_one_epoch_hash (spec_verify_epoch tsm).epoch_hashes
                                                              hv
                                                              e));
        return true
      ) else (
        rewrite (if b then _ else _)
                (exists_ (EpochMap.full_perm hashes M.init_epoch_hash));
        return false
      )

    | EpochMap.Found dst ->

      rewrite (EpochMap.get_post _ _ _ _ _ _)
              (EpochMap.perm hashes M.init_epoch_hash hv (PartialMap.upd EpochMap.empty_borrows e dst) `star`
               EH.epoch_hash_perm e dst (Map.sel hv e));
      let src = EpochMap.get t.epoch_hashes e in
      match src with
      | EpochMap.NotFound
      | EpochMap.Fresh ->
        rewrite (EpochMap.get_post _ _ _ t.epoch_hashes _ _)
                (EpochMap.full_perm t.epoch_hashes M.init_epoch_hash tsm.epoch_hashes);
        EpochMap.ghost_put hashes e dst _;
        intro_exists_erased hv (EpochMap.full_perm hashes M.init_epoch_hash);
        return false

      | EpochMap.Found src ->

        rewrite (EpochMap.get_post _ _ _ _ _ _)
                (EpochMap.perm t.epoch_hashes M.init_epoch_hash tsm.epoch_hashes (PartialMap.upd EpochMap.empty_borrows e src) `star`
                 EH.epoch_hash_perm e src (Map.sel tsm.epoch_hashes e));
        let b = aggregate_epoch_hashes_t src dst in
        if b
        then (
          rewrite (if b then _ else _)
                  (EH.epoch_hash_perm e dst (AEH.aggregate_epoch_hash
                                               (Map.sel hv e)
                                               (Map.sel tsm.epoch_hashes e)));
          EpochMap.ghost_put t.epoch_hashes e src _; //this should be a ghost put
          EpochMap.ghost_put hashes e dst _;
          return true
        )
        else (
          rewrite (if b then _ else _)
                  (exists_ (EH.epoch_hash_perm e dst));
          let vv = elim_exists #_ #_ #(EH.epoch_hash_perm e dst) () in
          assert_ (EH.epoch_hash_perm e dst vv);
          EpochMap.ghost_put t.epoch_hashes e src _; //this should be a ghost put
          EpochMap.ghost_put hashes e dst _;
          assert_ (EpochMap.full_perm hashes M.init_epoch_hash (Map.upd hv e vv));
          intro_exists (Map.upd hv e vv) (EpochMap.full_perm hashes M.init_epoch_hash);
          return false
        )

let update_bitmap_spec (bm:EpochMap.repr AEH.tid_bitmap)
                       (e:M.epoch_id)
                       (tid:tid)
  : EpochMap.repr AEH.tid_bitmap
  = Map.upd bm e (Seq.upd (Map.sel bm e) (U16.v tid) true)

/// Update the bitmap for tid indicating that it's epoch contribution
/// is ready
let update_bitmap (#bm:erased _)
                  (tid_bitmaps: AEH.epoch_tid_bitmaps)
                  (e:M.epoch_id)
                  (tid:tid)
  : STT bool
    (EpochMap.full_perm tid_bitmaps AEH.all_zeroes bm)
    (fun b ->
      EpochMap.full_perm tid_bitmaps AEH.all_zeroes
                  (update_if b
                             (reveal bm)
                             (update_bitmap_spec bm e tid)))
  = [@@inline_let]
    let update_tid (v:larray bool n_threads)
      : STT unit
            (array_pts_to v (Map.sel bm e))
            (fun _ -> array_pts_to v (Seq.upd (Map.sel bm e) (U16.v tid) true))
      = A.write v (as_u32 tid) true;
        ()
    in
    with_value_of_key tid_bitmaps e update_tid

let update_logs_of_tid
         (mlogs_v:AEH.all_processed_entries)
         (tsm:M.thread_state_model)
  : GTot AEH.all_processed_entries
  = Seq.upd mlogs_v (U16.v tsm.thread_id) tsm.processed_entries

let map_of_seq_update_lemma  (mlogs_v:AEH.all_processed_entries)
                             (tsm:M.thread_state_model)
  : Lemma (Map.equal (Map.upd (Map.upd (AEH.map_of_seq mlogs_v) tsm.thread_id None)
                              tsm.thread_id
                              (Some (spec_verify_epoch tsm).processed_entries))
                     (AEH.map_of_seq (update_logs_of_tid mlogs_v (spec_verify_epoch tsm))))
  = ()

/// A key ghost step:
///
///   Update the thread local log and then propagate the updated to
///   the anchored global state
let commit_entries #o
                   (#tsm:M.thread_state_model)
                   (#mlogs_v:AEH.all_processed_entries)
                   (t:thread_state_t)
                   (mylogref:TLM.t)
  : STGhost unit o
     (TLM.tid_pts_to mylogref t.thread_id full tsm.processed_entries false `star`
      TLM.global_anchor mylogref (AEH.map_of_seq mlogs_v) `star`
      G.pts_to t.processed_entries full (M.verifyepoch tsm).processed_entries)
     (fun _ ->
      TLM.tid_pts_to mylogref t.thread_id full (spec_verify_epoch tsm).processed_entries false `star`
      TLM.global_anchor mylogref (AEH.map_of_seq (update_logs_of_tid mlogs_v (spec_verify_epoch tsm))) `star`
      G.pts_to t.processed_entries full (spec_verify_epoch tsm).processed_entries)
     (requires
       t.thread_id == tsm.thread_id /\
       not tsm.failed /\
       not (M.verifyepoch tsm).failed)
     (ensures fun _ -> True)
  = TLM.take_anchor_tid mylogref _ _ _ _;
    M.committed_entries_idem (spec_verify_epoch tsm).processed_entries;
    TLM.update_anchored_tid_log mylogref _ _ (spec_verify_epoch tsm).processed_entries;
    TLM.put_anchor_tid mylogref _ _ _ _;
    G.write t.processed_entries (spec_verify_epoch tsm).processed_entries;
    map_of_seq_update_lemma mlogs_v tsm;
    rewrite
          (TLM.global_anchor mylogref _)
          (TLM.global_anchor mylogref (AEH.map_of_seq (update_logs_of_tid mlogs_v (spec_verify_epoch tsm))))

#push-options "--fuel 2"
let spec_verify_epoch_entries_invariants (tsm:M.thread_state_model)
  : Lemma
    (requires not tsm.failed /\
              not (spec_verify_epoch tsm).failed /\
              tsm_entries_invariant tsm)
    (ensures (tsm_entries_invariant (spec_verify_epoch tsm)))
  = assert (tsm == M.verify_model (M.init_thread_state_model tsm.thread_id) tsm.processed_entries);
    let tsm' = spec_verify_epoch tsm in
    assert (tsm'.processed_entries == Seq.snoc tsm.processed_entries VerifyEpoch);
    assert (Zeta.SeqAux.prefix tsm'.processed_entries
                               (Seq.length tsm.processed_entries)
            `Seq.equal`
           tsm.processed_entries);
    assert (tsm' == M.verify_model (M.init_thread_state_model tsm.thread_id) tsm'.processed_entries)
#pop-options

let advance_per_thread_bitmap_and_max  (bitmaps:EpochMap.repr AEH.tid_bitmap)
                                       (max:_)
                                       (mlogs_v:_)
                                       (tsm:M.thread_state_model)
                                       (e:M.epoch_id)
  : Lemma
    (requires (
      let tsm' = spec_verify_epoch tsm in
      AEH.per_thread_bitmap_and_max bitmaps max mlogs_v tsm.thread_id /\
      tsm'.last_verified_epoch == e /\
      not tsm'.failed /\
      tsm_entries_invariant tsm /\
      M.committed_entries tsm == AEH.log_of_tid mlogs_v tsm.thread_id
      ))
    (ensures (
      let tsm' = spec_verify_epoch tsm in
      let bitmaps' = update_bitmap_spec bitmaps e tsm.thread_id in
      let logs' = update_logs_of_tid mlogs_v tsm' in
      AEH.per_thread_bitmap_and_max bitmaps' max logs' tsm.thread_id))
  = let log0 = AEH.log_of_tid mlogs_v tsm.thread_id in
    let tsm0 = M.verify_model (M.init_thread_state_model tsm.thread_id) log0 in
    M.last_verified_epoch_constant tsm;
    assert (tsm0.last_verified_epoch == tsm.last_verified_epoch);
    let tsm' = spec_verify_epoch tsm in
    let bitmaps' = update_bitmap_spec bitmaps e tsm.thread_id in
    let logs' = update_logs_of_tid mlogs_v tsm' in
    spec_verify_epoch_entries_invariants tsm
    // assert (U32.v max <= U32.v tsm0.last_verified_epoch);
    // assert (U32.v e == U32.v tsm.last_verified_epoch + 1);
    // assert (U32.v max <= U32.v tsm'.last_verified_epoch)

let restore_all_threads_bitmap_and_max  (bitmaps:AEH.epoch_bitmaps_repr)
                                        (max:_)
                                        (mlogs_v:_)
                                        (tsm:M.thread_state_model)
                                        (e:M.epoch_id)
  : Lemma
    (requires
      (let tsm' = spec_verify_epoch tsm in
       (forall tid. AEH.per_thread_bitmap_and_max bitmaps max mlogs_v tid) /\
       tsm'.last_verified_epoch = e /\
       tsm_entries_invariant tsm /\
       not tsm'.failed /\
       M.committed_entries tsm == AEH.log_of_tid mlogs_v tsm.thread_id))
    (ensures
      (let tsm' = spec_verify_epoch tsm in
        (forall tid. AEH.per_thread_bitmap_and_max
                      (update_bitmap_spec bitmaps e tsm.thread_id)
                      max
                      (update_logs_of_tid mlogs_v tsm')
                      tid)))
  = advance_per_thread_bitmap_and_max bitmaps max mlogs_v tsm e
#push-options "--print_implicits --print_bound_var_types"
let lemma_restore_hashes_bitmaps_max_ok
                                  (hashes:AEH.epoch_hashes_repr)
                                  (bitmaps:AEH.epoch_bitmaps_repr)
                                  (max:option M.epoch_id)
                                  (mlogs_v:AEH.all_processed_entries)
                                  (tsm:M.thread_state_model)
                                  (e:M.epoch_id)
  : Lemma
    (requires
      (spec_verify_epoch tsm).last_verified_epoch = e /\
      AEH.hashes_bitmaps_max_ok hashes bitmaps max mlogs_v /\
      tsm_entries_invariant tsm /\
      not (spec_verify_epoch tsm).failed /\
      M.committed_entries tsm == AEH.log_of_tid mlogs_v tsm.thread_id)
    (ensures (
      let tsm' = spec_verify_epoch tsm in
      let hashes' = aggregate_one_epoch_hash tsm'.epoch_hashes hashes e in
      let bitmaps' = update_bitmap_spec bitmaps e tsm'.thread_id in
      let mlogs_v' = update_logs_of_tid mlogs_v tsm' in
      AEH.hashes_bitmaps_max_ok hashes' bitmaps' max mlogs_v'))
  = let log0 = AEH.log_of_tid mlogs_v tsm.thread_id in
    let tsm0 = M.verify_model (M.init_thread_state_model tsm.thread_id) log0 in
    let tsm' = spec_verify_epoch tsm in
    let hashes' = aggregate_one_epoch_hash tsm'.epoch_hashes hashes e in
    let bitmaps' = update_bitmap_spec bitmaps e tsm'.thread_id in
    let mlogs_v' = update_logs_of_tid mlogs_v tsm' in
    advance_per_thread_bitmap_and_max bitmaps max mlogs_v tsm e;
    introduce forall (e':M.epoch_id).
      Map.sel hashes' e' == AEH.aggregate_all_threads_epoch_hashes e' mlogs_v'
    with (
      if e = e'
      then (
        calc (==) {
         AEH.aggregate_all_threads_epoch_hashes e mlogs_v';
         (==) { _ by FStar.Tactics.(trefl()) }
         Zeta.SeqAux.reduce #(AEH.epoch_hashes_repr) M.init_epoch_hash
                       (fun s -> AEH.aggregate_epoch_hash (Map.sel s e))
                       (AEH.all_threads_epoch_hashes_of_logs mlogs_v');
         (==) {admit()} //probably easier to do this using the permutation monoid
                             //and we need to know that the bit for tsm was false initially
         AEH.aggregate_epoch_hash (AEH.aggregate_all_threads_epoch_hashes e mlogs_v)
                                  (Map.sel tsm'.epoch_hashes e);
        }
      )
      else (
        assert (Map.sel hashes' e' == Map.sel hashes e');
        assert (Map.sel hashes e' == AEH.aggregate_all_threads_epoch_hashes e' mlogs_v);
        //need a framing lemma here
        // -- we only updated the logs of tsm'
        // -- the only epoch that was propagated was e, since mlogs_v contained all prior committed epoch
        // -- so, only the epoch contents of e changed, not e'
        assume (AEH.aggregate_all_threads_epoch_hashes e' mlogs_v ==
                AEH.aggregate_all_threads_epoch_hashes e' mlogs_v')
      )
    );
    //assert (U32.v max <= U32.v tsm0.last_verified_epoch);
    M.last_verified_epoch_constant tsm

let restore_hashes_bitmaps_max_ok (#o:_)
                                  (#hashes:AEH.epoch_hashes_repr)
                                  (#bitmaps:AEH.epoch_bitmaps_repr)
                                  (#max:option M.epoch_id)
                                  (#mlogs_v:AEH.all_processed_entries)
                                  (tsm:M.thread_state_model)
                                  (e:M.epoch_id)
  : STGhost unit o
    (pure (AEH.hashes_bitmaps_max_ok hashes bitmaps max mlogs_v))
    (fun _ ->
      let tsm' = spec_verify_epoch tsm in
      let hashes' = aggregate_one_epoch_hash tsm'.epoch_hashes hashes e in
      let bitmaps' = update_bitmap_spec bitmaps e tsm'.thread_id in
      let mlogs_v' = update_logs_of_tid mlogs_v tsm' in
      pure (AEH.hashes_bitmaps_max_ok hashes' bitmaps' max mlogs_v'))
    (requires
          M.committed_entries tsm == AEH.log_of_tid mlogs_v tsm.thread_id /\
          (spec_verify_epoch tsm).last_verified_epoch = e /\
          tsm_entries_invariant tsm /\
          not (spec_verify_epoch tsm).failed)
    (ensures fun _ -> True)
  = elim_pure _;
    lemma_restore_hashes_bitmaps_max_ok hashes bitmaps max mlogs_v tsm e;
    intro_pure _

////////////////////////////////////////////////////////////////////////////////
// Finally verify_epoch itself
////////////////////////////////////////////////////////////////////////////////
let verify_epoch_core
                 (#tsm:M.thread_state_model)
                 (t:thread_state_t)
                 (hashes : AEH.all_epoch_hashes)
                 (tid_bitmaps : AEH.epoch_tid_bitmaps)
                 (max_certified_epoch : R.ref (option M.epoch_id))
                 (mlogs: TLM.t)
                 (lock: cancellable_lock (AEH.lock_inv hashes tid_bitmaps max_certified_epoch mlogs))
  : ST bool
    (thread_state_inv_core t tsm `star`
     TLM.tid_pts_to mlogs t.thread_id full tsm.processed_entries false)
    (fun b ->
      thread_state_inv_core t (update_if b tsm (spec_verify_epoch tsm)) `star`
      TLM.tid_pts_to mlogs t.thread_id full (update_if b tsm.processed_entries
                                                         (spec_verify_epoch tsm).processed_entries)
                                            false)
    (requires
      t.thread_id == tsm.thread_id /\
      tsm_entries_invariant tsm /\
      not tsm.failed)
    (ensures fun _ -> True)
  = let e = R.read t.last_verified_epoch in
    let e' = st_check_overflow_add32 e 1ul in
    match e' with
    | None ->
      R.write t.failed true; return true

    | Some e ->
      let acquired = acquire lock in
      if not acquired
      then (
        rewrite (maybe_acquired _ _)
                emp;
        return false
      )
      else (
        rewrite (maybe_acquired acquired lock)
                (AEH.lock_inv hashes tid_bitmaps max_certified_epoch mlogs `star` can_release lock);
        let _hv = elim_exists () in
        let _bitmaps = elim_exists () in
        let _max = elim_exists () in
        let _mlogs_v =
          elim_exists #_ #_
            #(AEH.lock_inv_body hashes tid_bitmaps max_certified_epoch mlogs
                                _hv _bitmaps _max)
            ()
        in
        TLM.extract_anchor_invariant mlogs _ _ _ _;
        let b0 = propagate_epoch_hash t hashes e in
        let b1 = update_bitmap tid_bitmaps e t.thread_id in
        if not b0 || not b1
        then ( //propagation failed, e.g., due to overflow
           cancel lock;
           drop _; //drop resources protected by lock; invariant is lost
           return false
        )
        else (
           R.write t.last_verified_epoch e;
           assert_ (thread_state_inv_core t (M.verifyepoch tsm));
           assert ((spec_verify_epoch tsm).last_verified_epoch == e);
           commit_entries t mlogs;
           restore_hashes_bitmaps_max_ok tsm e;
           rewrite (if b0 then _ else _)
                   (EpochMap.full_perm hashes M.init_epoch_hash (aggregate_one_epoch_hash (spec_verify_epoch tsm).epoch_hashes _hv e));
           AEH.release_lock #(hide (aggregate_one_epoch_hash (spec_verify_epoch tsm).epoch_hashes _hv e))
                            #(hide (update_bitmap_spec _bitmaps e (spec_verify_epoch tsm).thread_id))
                            lock;
           return true
        )
      )

////////////////////////////////////////////////////////////////////////////////

let verify_epoch (#tsm:M.thread_state_model)
                 (t:thread_state_t)
                 (aeh:AEH.aggregate_epoch_hashes)
  = elim_thread_state_inv #_ #tsm t;
    rewrite (TLM.tid_pts_to _ _ _ _ _)
            (TLM.tid_pts_to aeh.mlogs t.thread_id full tsm.processed_entries false);
    let b = verify_epoch_core t aeh.hashes aeh.tid_bitmaps aeh.max_certified_epoch aeh.mlogs aeh.lock in
    rewrite (TLM.tid_pts_to _ _ _ _ _)
            (TLM.tid_pts_to aeh.mlogs tsm.thread_id full (update_if b tsm.processed_entries
                                                                    (M.verify_step_model tsm VerifyEpoch).processed_entries) false);
    M.tsm_entries_invariant_verify_step tsm VerifyEpoch;
    intro_thread_state_inv t;
    return b
