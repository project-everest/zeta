module Zeta.Steel.Verifier
friend Zeta.Steel.VerifierTypes
open Zeta.Steel.VerifierTypes
open FStar.Ghost
open Steel.ST.Util
module G = Steel.ST.GhostReference
module R = Steel.ST.Reference
module A = Steel.ST.Array
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
module P = Zeta.Steel.Parser

module Cast = FStar.Int.Cast
let as_u32 (s:U16.t) : U32.t = Cast.uint16_to_uint32 s
#push-options "--ide_id_info_off"

let spec_parser_log  = admit()

assume
val admit__ (#a:Type)
            (#p:pre_t)
            (#q:post_t a)
            (_:unit)
  : STF a p q True (fun _ -> False)

let finalize_epoch_hash
  : IArray.finalizer AEH.epoch_hash_perm
  = fun k v -> drop _ //TODO: Actually free it

let create (tid:T.thread_id)
  : STT thread_state_t
    emp
    (fun t -> thread_state_inv t (M.init_thread_state_model tid))
  = let failed = R.alloc false in
    let store : vstore = A.alloc None (as_u32 store_size) in
    let clock = R.alloc 0uL in
    let epoch_hashes = IArray.create AEH.epoch_id_hash 64ul finalize_epoch_hash in
    let processed_entries : G.ref (Seq.seq log_entry_base) = G.alloc Seq.empty in
    let app_results : G.ref M.app_results = G.alloc Seq.empty in
    let serialization_buffer = A.alloc 0uy 4096ul in
    let tsm = M.init_thread_state_model tid in
    let t : thread_state_t = {
        thread_id = tid;
        failed;
        store;
        clock;
        epoch_hashes;
        processed_entries;
        app_results;
        serialization_buffer
    } in
    intro_exists _ (A.pts_to serialization_buffer);
    intro_pure (tsm == M.verify_model tsm Seq.empty);
    rewrite (R.pts_to failed _ _ `star`
             A.pts_to store _ `star`
             R.pts_to clock _ _ `star`
             IArray.perm epoch_hashes _ _ `star`
             G.pts_to processed_entries _ _ `star`
             G.pts_to app_results _ _ `star`
             exists_ (A.pts_to serialization_buffer) `star`
             pure (tsm == M.verify_model tsm Seq.empty)
            )
            (thread_state_inv t (M.init_thread_state_model tid));
    return t

////////////////////////////////////////////////////////////////////////////////
// Just a couple of warm ups, we don't actually need this
////////////////////////////////////////////////////////////////////////////////
#push-options "--query_stats --fuel 0 --ifuel 1"

let tsm_t (tsm:M.thread_state_model) =
    t:thread_state_t { t.thread_id == tsm.thread_id}

[@@__reduce__]
let thread_state_inv' (t:thread_state_t)
                      ([@@@smt_fallback] tsm:M.thread_state_model)
  : vprop
  = R.pts_to t.failed full tsm.failed `star`
    A.pts_to t.store tsm.store `star`
    R.pts_to t.clock full tsm.clock `star`
    IArray.perm t.epoch_hashes tsm.epoch_hashes Set.empty `star`
    G.pts_to t.processed_entries full tsm.processed_entries `star`
    G.pts_to t.app_results full tsm.app_results `star`
    exists_ (A.pts_to t.serialization_buffer)

let intro_thread_state_inv #o
                           (tsm:M.thread_state_model)
                           (#f:_)
                           (#s:_)
                           (#c:_)
                           (#eh:_)
                           (#pe:_)
                           (#ar:_)
                           (t:thread_state_t)
   : STGhost unit o
     (R.pts_to t.failed full f `star`
      A.pts_to t.store s `star`
      R.pts_to t.clock full c `star`
      IArray.perm t.epoch_hashes eh Set.empty `star`
      G.pts_to t.processed_entries full pe `star`
      G.pts_to t.app_results full ar `star`
      exists_ (A.pts_to t.serialization_buffer))
     (fun _ -> thread_state_inv' t tsm)
     (requires
       tsm.failed == f /\
       tsm.store == s /\
       tsm.clock == c /\
       tsm.epoch_hashes == eh /\
       tsm.processed_entries == pe /\
       tsm.app_results == ar)
     (ensures fun _ ->
       True)
   = rewrite (R.pts_to t.failed _ _ `star`
              A.pts_to t.store _ `star`
              R.pts_to t.clock _ _ `star`
              IArray.perm t.epoch_hashes _ _ `star`
              G.pts_to t.processed_entries _ _ `star`
              G.pts_to t.app_results _ _ `star`
              exists_ (A.pts_to t.serialization_buffer))
             (thread_state_inv' t tsm)

let fail (#tsm:M.thread_state_model)
         (t:thread_state_t)
  : STT unit
    (thread_state_inv' t tsm)
    (fun _ -> thread_state_inv' t (M.fail tsm))
  = R.write t.failed true

let vget (#tsm:M.thread_state_model)
         (t:thread_state_t)
         (s:slot)
         (k:key)
         (v:M.data_value)
  : STT unit
    (thread_state_inv' t tsm)
    (fun _ -> thread_state_inv' t (M.vget tsm s k v))
  = let se_opt = A.read t.store (as_u32 s) in
    match se_opt with
    | None ->
        R.write t.failed true; ()
    | Some r ->
        if r.key <> k
        then (R.write t.failed true; ())
        else if r.value <> DValue v
        then (R.write t.failed true; ())
        else (noop(); ())

let vput (#tsm:M.thread_state_model)
         (t:thread_state_t)
         (s:slot)
         (k:key)
         (v:M.data_value)
  : STT unit
    (thread_state_inv' t tsm)
    (fun _ -> thread_state_inv' t (M.vput tsm s k v))
  = let se_opt = A.read t.store (as_u32 s) in
    match se_opt with
    | None ->
      R.write t.failed true; ()
    | Some r ->
      if r.key <> k
      then (R.write t.failed true; ())
      else if not (ApplicationKey? k)
      then (R.write t.failed true; ())
      else (A.write t.store (as_u32 s) (Some ({r with M.value = DValue v}));
            ())
module KU = Zeta.Steel.KeyUtils

let entry_points_to_some_slot (r:M.store_entry)
                              (d:bool)
  : bool
  = if d
    then Some? (r.l_child_in_store)
    else Some? (r.r_child_in_store)

let update_value (#tsm:M.thread_state_model)
                 (t:thread_state_t)
                 (s:slot { M.has_slot tsm s })
                 (r:value { M.is_value_of (M.key_of_slot tsm s) r})
  : STT unit
    (thread_state_inv' t tsm)
    (fun _ -> thread_state_inv' t (M.update_value tsm s r))
  = let Some v = A.read t.store (as_u32 s) in
    A.write t.store (as_u32 s) (Some ({v with M.value = r}));
    ()

let evict_from_store (#tsm:M.thread_state_model)
                     (t:thread_state_t)
                     (s:slot)
                     (s':slot { M.has_slot tsm s' })
                     (d:bool)
  : STT unit
    (thread_state_inv' t tsm)
    (fun _ -> thread_state_inv' t (M.mevict_from_store tsm s s' d))
  = let Some r' = A.read t.store (as_u32 s') in
    let e' =
        if d
        then { r' with M.l_child_in_store = None }
        else { r' with M.r_child_in_store = None }
    in
    A.write t.store (as_u32 s') (Some e');
    A.write t.store (as_u32 s) None;
    ()


let vevictm (#tsm:M.thread_state_model)
            (t:thread_state_t)
            (s s':slot_id)
  : STT unit
    (thread_state_inv' t tsm)
    (fun _ -> thread_state_inv' t (M.vevictm tsm s s'))
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


let sat_evictb_checks (#tsm:M.thread_state_model)
                      (t:thread_state_t)
                      (s:slot)
                      (ts:timestamp)
  : ST bool
    (thread_state_inv' t tsm)
    (fun _ -> thread_state_inv' t tsm)
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

module HA = Zeta.Steel.HashAccumulator
assume
val ha_add (#v:erased (HA.hash_value_t))
           (ha:HA.ha)
           (l:U32.t)
           (#bs:erased bytes { U32.v l <= Seq.length bs /\ U32.v l <= HA.blake2_max_input_length })
           (input:A.array U8.t)
  : STT bool
       (HA.ha_val ha v `star` A.pts_to input bs)
       (fun b ->
         A.pts_to input bs `star`
         HA.ha_val ha (HA.maybe_aggregate_hashes b v
                         (HA.hash_one_value (Seq.slice bs 0 (U32.v l)))))


let unfold_epoch_hash_perm #o (k:M.epoch_id) (v:AEH.epoch_hashes_t) (c:M.epoch_hash)
  : STGhost unit o
    (AEH.epoch_hash_perm k v c)
    (fun _ ->
      HA.ha_val v.hadd c.hadd `star`
      HA.ha_val v.hevict c.hevict)
    (requires True)
    (ensures fun _ ->
      reveal v.complete == c.epoch_complete)
  = rewrite (AEH.epoch_hash_perm k v c)
            (HA.ha_val v.hadd c.hadd `star`
             HA.ha_val v.hevict c.hevict `star`
             pure (reveal v.complete == c.epoch_complete));
    elim_pure _

let fold_epoch_hash_perm #o
                         (k:M.epoch_id)
                         (v:AEH.epoch_hashes_t)
                         (#had #hev:HA.hash_value_t)
                         (c:M.epoch_hash)
  : STGhost unit o
    (HA.ha_val v.hadd had `star`
     HA.ha_val v.hevict hev)
    (fun _ -> AEH.epoch_hash_perm k v c)
    (requires
      c.hadd == had /\
      c.hevict == hev /\
      reveal v.complete == c.epoch_complete)
    (ensures fun _ -> True)
  = intro_pure (reveal v.complete == c.epoch_complete);
    rewrite (HA.ha_val v.hadd had `star`
             HA.ha_val v.hevict hev `star`
             pure _)
            (AEH.epoch_hash_perm k v c)

type htype =
  | HAdd
  | HEvict

let update_if (b:bool) (default_ upd_: 'a)
  : 'a
  = if b then upd_ else default_

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

let set_add_remove (#a:eqtype) (s:Set.set a) (x:a)
  : Lemma (requires not (Set.mem x s))
          (ensures IArray.set_remove (IArray.set_add s x) x == s)
  = let lhs = IArray.set_remove (IArray.set_add s x) x in
    Set.lemma_equal_intro lhs s;
    assert (lhs `Set.equal` s)

#push-options "--z3rlimit_factor 2"
let update_ht (#tsm:M.thread_state_model)
              (t:thread_state_t)
              (e:M.epoch_id)
              (r:T.record)
              (ts:T.timestamp)
              (thread_id:T.thread_id)
              (ht:htype)
  : STT bool
    (thread_state_inv' t tsm)
    (fun b -> thread_state_inv' t (update_if b tsm (update_epoch_hash tsm e r ts thread_id ht)))
  = let vopt = IArray.get t.epoch_hashes e in
    set_add_remove Set.empty e;
    match vopt with
    | None ->
      rewrite (IArray.get_post _ _ _ _ vopt)
              (IArray.perm t.epoch_hashes tsm.epoch_hashes Set.empty);
      return false

    | Some v ->
      rewrite (IArray.get_post _ _ _ _ vopt)
              (AEH.epoch_hash_perm e v (Map.sel tsm.epoch_hashes e) `star`
               IArray.perm t.epoch_hashes tsm.epoch_hashes (IArray.set_add Set.empty e));
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
                            A.pts_to t.serialization_buffer bs
                            )
                           (fun b ->
                             A.pts_to t.serialization_buffer bs `star`
                             AEH.epoch_hash_perm e v
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
      IArray.put t.epoch_hashes e v _;
      rewrite (IArray.perm _ _ _)
              (IArray.perm t.epoch_hashes
                           (Map.upd tsm.epoch_hashes e
                                   (update_if b (Map.sel tsm.epoch_hashes e)
                                                (update_hash (Map.sel tsm.epoch_hashes e) r ts thread_id ht)))
                           Set.empty);
      intro_exists _ (A.pts_to t.serialization_buffer);
      maybe_update_epoch_hash_equiv b tsm e r ts thread_id ht;
      rewrite (thread_state_inv' t (maybe_update_epoch_hash b tsm e r ts thread_id ht))
              (thread_state_inv' t (update_if b tsm (update_epoch_hash tsm e r ts thread_id ht)));
      return b
#pop-options

let vevictb_update_hash_clock (#tsm:M.thread_state_model)
                              (t:thread_state_t)
                              (s:slot)
                              (ts:timestamp { M.sat_evictb_checks tsm s ts })
   : ST bool
     (thread_state_inv' t tsm)
     (fun b -> thread_state_inv' t (update_if b tsm (M.vevictb_update_hash_clock tsm s ts)))
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
//       intro_thread_state_inv (M.vevictb_update_hash_clock tsm s ts) t;
       return b
     )
     else (
       rewrite (thread_state_inv' t _) (thread_state_inv' t tsm);
       return b
     )

let vevictb (#tsm:M.thread_state_model)
            (t:thread_state_t)
            (s:slot_id)
            (ts:timestamp)
  : ST bool
    (thread_state_inv' t tsm)
    (fun b -> thread_state_inv' t (update_if b tsm (M.vevictb tsm s ts)))
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
            rewrite (thread_state_inv' t _)
                    (thread_state_inv' t tsm);
            return false
          )
        )
      )
    )

let fail_as (#tsm:M.thread_state_model)
            (t:thread_state_t)
            (tsm':M.thread_state_model)
  : ST bool
    (thread_state_inv' t tsm)
    (fun b -> thread_state_inv' t (update_if b tsm tsm'))
    (requires tsm' == M.fail tsm)
    (ensures fun _ -> True)
  = R.write t.failed true;
    let b = true in
    intro_thread_state_inv (update_if b tsm tsm') t;
    return b

let vevictbm (#tsm:M.thread_state_model)
             (t:thread_state_t)
             (s s':slot_id)
             (ts:timestamp)
  : ST bool
    (thread_state_inv' t tsm)
    (fun b -> thread_state_inv' t (update_if b tsm (M.vevictbm tsm s s' ts)))
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
                          (STT bool (thread_state_inv' t tsm)
                                    (fun b -> thread_state_inv' t (update_if b tsm (M.vevictbm tsm s s' ts))))
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
                          // rewrite (thread_state_inv' t _)
                          //         (thread_state_inv' t (M.vevictb_update_hash_clock tsm s ts));
                          let mv'_upd = M.update_merkle_value mv' d k h2 true in
                          update_value t s' (MValue mv'_upd);
                          evict_from_store t s s' d;
                          return true
                        )
                        else (
                          rewrite (thread_state_inv' t _)
                                  (thread_state_inv' t tsm);
                          return false
                        ))))

let check_overflow_add (x y:U64.t)
  : res:option U64.t {
        if FStar.UInt.fits (U64.v x + U64.v y) 64
        then Some? res /\
             Some?.v res == U64.add x y
        else None? res
    }
 = let open U64 in
   let res = U64.add_mod x y in
   if res <^ x then None
   else if res -^ x = y then Some res
   else None


let check_overflow_add32 (x y:U32.t)
  : Pure (option U32.t)
    (requires True)
    (ensures fun res ->
        if FStar.UInt.fits (U32.v x + U32.v y) 32
        then Some? res /\
             Some?.v res == U32.add x y
        else None? res)
 = let open U64 in
   let res = U64.(Cast.uint32_to_uint64 x +^
                  Cast.uint32_to_uint64 y)
   in
   if res >^ 0xffffffffuL
   then None
   else (assert (U64.v res  == U32.v x + U32.v y);
         assert (U64.v res <= pow2 32);
         let res = Cast.uint64_to_uint32 res in
         assert (U32.v res  == U32.v x + U32.v y);
         Some res)

let st_check_overflow_add32 (x y:U32.t)
  : ST (option U32.t)
       emp
       (fun _ -> emp)
       (requires True)
       (ensures fun res ->
         if FStar.UInt.fits (U32.v x + U32.v y) 32
         then Some? res /\
              Some?.v res == U32.add x y
         else None? res)
  = let r = check_overflow_add32 x y in return r

let new_epoch (e:M.epoch_id)
  : STT AEH.epoch_hashes_t
    emp
    (fun v -> AEH.epoch_hash_perm e v M.init_epoch_hash)
  = admit__()

let nextepoch (#tsm:M.thread_state_model)
              (t:thread_state_t)
  : STT unit
    (thread_state_inv' t tsm)
    (fun _ -> thread_state_inv' t (M.nextepoch tsm))
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
      IArray.put t.epoch_hashes nxt eht M.init_epoch_hash;
      assert (IArray.set_remove Set.empty nxt `Set.equal` Set.empty);
      rewrite (IArray.perm _ _ _)
              (IArray.perm t.epoch_hashes (Map.upd tsm.epoch_hashes nxt M.init_epoch_hash) (Set.empty));
      ()

let next (t:T.timestamp)
  : option T.timestamp
  = if FStar.UInt.fits (U64.v t + 1) 64
    then Some (U64.add t 1uL)
    else None



// let vaddb (#tsm:M.thread_state_model)
//           (t:thread_state_t)
//           (s:slot_id)
//           (ts:T.timestamp)
//           (tid:T.thread_id)
//           (p:M.payload)
//   : STT unit
//     (thread_state_inv' t tsm)
//     (fun _ -> thread_state_inv' t (M.vaddb tsm s ts tid p))
//   = if not (M.check_slot_bounds s)
//     then (R.write t.failed true; ())
//     else (
//       match record_of_payload p with
//       | None ->
//         R.write t.failed true; ()
//         fail tsm //parsing failure
//       | Some (| k, v |) ->
//         if is_root_key k
//         then (fail t; intro_ //root key
//         else if Some? (get_entry tsm s) then fail tsm //slot is already full
//         else (
//         //add hash (k, v, t, thread_id) to hadd.[epoch_of_timestamp t]
//         let tsm = update_hadd tsm (epoch_of_timestamp t) (k, v) t thread_id in
//         match next t with //increment the time
//         | None ->
//           fail tsm //overflow
//         | Some t' ->
//           let tsm = update_clock tsm (max tsm.clock t') in
//           put_entry tsm s (mk_entry k v BAdd)
//       )


// val serialized_new_app_results (init final:M.app_results)
//                                (n_out:U32.t)
//                                (out: P.bytes)
//   : prop

// let delta_app_results (tsm0 tsm1:M.thread_state_model)
//   : GTot (Seq.seq M.app_results)
//   = Prims.admit()

// let bytes_of_app_results (s:Seq.seq M.app_results)
//   : GTot bytes
//   = Prims.admit()

// /// Entry point to run a single verifier thread on a log
let verify (#tsm:M.thread_state_model)
           (t:thread_state_t) //handle to the thread state
           (#log_bytes:erased bytes)
           (#len:U32.t)
           (log:larray U8.t len) //concrete log
           (#outlen:U32.t)
           (out:larray U8.t outlen) //out array, to write outputs
           (#logrefs: erased (AEH.log_refs_t))
           (aeh:AEH.aggregate_epoch_hashes logrefs) //lock & handle to the aggregate state
           (mylogref:AEH.log_ref { //this thread's contribution to the aggregate state
             Map.sel logrefs tsm.thread_id == mylogref
            })
  = admit__()
