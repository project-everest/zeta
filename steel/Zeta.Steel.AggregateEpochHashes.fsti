module Zeta.Steel.AggregateEpochHashes

open FStar.Ghost
open Steel.ST.Util
module A = Steel.ST.Array
module R = Steel.ST.Reference
module G = Steel.ST.GhostReference
module Lock = Steel.ST.SpinLock
open Zeta.Steel.ApplicationTypes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Zeta.Steel.FormatsManual
module IArray = Zeta.Steel.IArray
module T = Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel
module HA = Zeta.Steel.HashAccumulator
open Zeta.Steel.Util
module MR = Steel.ST.MonotonicReference
module TLM = Zeta.Steel.ThreadLogMap
#push-options "--ide_id_info_off"

/// Initializer for an IArray
val epoch_hash_size : U32.t

noeq
type epoch_hashes_t = {
  hadd: HA.ha;
  hevict: HA.ha;
}

let epoch_hashes_repr = IArray.repr M.epoch_id M.epoch_hash
let epoch_id_hash (x:M.epoch_id) : U32.t = x
let epoch_hash_perm (k:M.epoch_id)
                    (v:epoch_hashes_t)
                    (c:M.epoch_hash) =
    HA.ha_val v.hadd c.hadd `star`
    HA.ha_val v.hevict c.hevict

let all_epoch_hashes =
  IArray.tbl
    #M.epoch_id
    #epoch_hashes_t
    #M.epoch_hash
    epoch_id_hash
    epoch_hash_perm

let tid_bitmap = Seq.lseq bool (U32.v n_threads)
let epoch_tid_bitmaps =
  IArray.tbl
    #M.epoch_id
    #(larray bool n_threads)
    #tid_bitmap
    epoch_id_hash
    (fun i -> array_pts_to)

let is_epoch_verified (tsm:M.thread_state_model) (eid:M.epoch_id) =
  U32.v tsm.M.last_verified_epoch >= U32.v eid

let all_threads_epoch_hashes =
  Seq.lseq epoch_hashes_repr (U32.v n_threads)

let aggregate_epoch_hash (e0 e1:M.epoch_hash)
  : M.epoch_hash
  = { hadd = HA.aggregate_hashes e0.hadd e1.hadd;
      hevict = HA.aggregate_hashes e0.hevict e1.hevict}

let log = Seq.seq log_entry_base
let all_processed_entries = Seq.lseq log (U32.v n_threads)

let tsm_of_log (mlogs_v:all_processed_entries) (t:tid) =
  M.verify_model (M.init_thread_state_model t)
                 (Seq.index mlogs_v (U16.v t))

let thread_contrib_of_log (t:tid) (l:log)
  : epoch_hashes_repr
  = let tsm = M.verify_model (M.init_thread_state_model t) l in
    Zeta.Steel.Util.map_literal
      (fun (e:M.epoch_id) ->
         if is_epoch_verified tsm e
         then Map.sel tsm.epoch_hashes e
         else M.init_epoch_hash)

let all_threads_epoch_hashes_of_logs (mlogs_v:all_processed_entries)
  : all_threads_epoch_hashes
  = Zeta.SeqAux.mapi mlogs_v
                     (fun tid -> thread_contrib_of_log (U16.uint_to_t tid) (Seq.index mlogs_v tid))

let aggregate_all_threads_epoch_hashes (e:M.epoch_id)
                                       (mlogs_v:all_processed_entries)
  : M.epoch_hash
  = Zeta.SeqAux.reduce M.init_epoch_hash
                       (fun (s:epoch_hashes_repr) -> aggregate_epoch_hash (Map.sel s e))
                       (all_threads_epoch_hashes_of_logs mlogs_v)

(* Global monotonic log of entries *)


let map_of_seq (a:all_processed_entries)
  : TLM.repr
  = FStar.Map.map_literal (fun (tid:tid) -> Some (Seq.index a (U16.v tid)))

let log_of_tid (a:all_processed_entries) (t:tid) = Seq.index a (U16.v t)

let committed_tsm_of_logs (mlogs_v:all_processed_entries) (t:tid) =
   M.verify_model (M.init_thread_state_model t)
                  (M.committed_log_entries (log_of_tid mlogs_v t))

let all_contributions_are_accurate (global:epoch_hashes_repr)
                                   (mlogs_v:all_processed_entries)
  : prop
  = forall (e:M.epoch_id). Map.sel global e == aggregate_all_threads_epoch_hashes e mlogs_v

let all_ones = Seq.create (U32.v n_threads) true

let max_certified_epoch_is (global:epoch_hashes_repr)
                           (bitmaps: IArray.repr M.epoch_id tid_bitmap)
                           (max:M.epoch_id)
  : prop
  = forall (e:M.epoch_id).
       U32.v e <= U32.v max ==>
       (Map.sel bitmaps e) == all_ones /\
       (Map.sel global e).hadd == (Map.sel global e).hevict


let epoch_is_complete (mlogs_v:all_processed_entries) (e:M.epoch_id)
  = forall tid. is_epoch_verified (tsm_of_log mlogs_v tid) e

let per_thread_bitmap_and_max (bitmaps: IArray.repr M.epoch_id tid_bitmap)
                              (max:M.epoch_id)
                              (all_logs:all_processed_entries)
                              (tid:tid)
  : prop
  = let tsm = M.verify_model (M.init_thread_state_model tid) (log_of_tid all_logs tid) in
    U32.v max <= U32.v tsm.last_verified_epoch /\ //max can't exceed the verified epoch ctr for tid
    (forall (eid:M.epoch_id).
      Seq.index (Map.sel bitmaps eid) (U16.v tid) == is_epoch_verified tsm eid)

let hashes_bitmaps_max_ok (hashes:epoch_hashes_repr)
                          (bitmaps: IArray.repr M.epoch_id tid_bitmap)
                          (max:M.epoch_id)
                          (mlogs_v:all_processed_entries)
 : prop
 = all_contributions_are_accurate hashes mlogs_v /\
   max_certified_epoch_is hashes bitmaps max /\
   (forall tid. per_thread_bitmap_and_max bitmaps max mlogs_v tid)



[@@__reduce__]
let lock_inv_body (hashes : all_epoch_hashes)
                  (tid_bitmaps : epoch_tid_bitmaps)
                  (max_certified_epoch : R.ref M.epoch_id)
                  (mlogs:TLM.t)
                  (hashes_v:_)
                  (bitmaps:_)
                  (max:_)
                  (mlogs_v:all_processed_entries)
  = IArray.perm hashes hashes_v `star`
    IArray.perm tid_bitmaps bitmaps `star`
    R.pts_to max_certified_epoch full max `star`
    TLM.global_anchor mlogs (map_of_seq mlogs_v) `star`
    pure (hashes_bitmaps_max_ok hashes_v bitmaps max mlogs_v)

let lock_inv (hashes : all_epoch_hashes)
             (tid_bitmaps : epoch_tid_bitmaps)
             (max_certified_epoch : R.ref M.epoch_id)
             (mlogs: TLM.t)
 : vprop
 = exists_ (fun hashes_v ->
   exists_ (fun bitmaps ->
   exists_ (fun max ->
   exists_ (fun (mlogs_v:all_processed_entries) ->
     lock_inv_body hashes tid_bitmaps max_certified_epoch mlogs
                   hashes_v bitmaps max mlogs_v))))

noeq
type aggregate_epoch_hashes = {
     hashes : all_epoch_hashes;
     tid_bitmaps : epoch_tid_bitmaps;
     max_certified_epoch : R.ref M.epoch_id;
     mlogs: TLM.t;
     lock: cancellable_lock (lock_inv hashes tid_bitmaps max_certified_epoch mlogs)
}
#push-options "--print_effect_args"
module EHT = Steel.ST.EphemeralHashtbl

let check_bitmap_for_epoch (#bm:erased _)
                           (tid_bitmaps: epoch_tid_bitmaps)
                           (e:M.epoch_id)
  : ST bool
    (IArray.perm tid_bitmaps bm)
    (fun b -> IArray.perm tid_bitmaps bm)
    (requires True)
    (ensures fun b -> b ==> Map.sel bm e == all_ones)
  = let fpost (bm_e bm_e':tid_bitmap) (b:bool) =
      pure (bm_e == bm_e' /\ (b ==> bm_e == all_ones))
    in
    let f (a:larray bool n_threads)
      : STT bool
            (emp `star` array_pts_to a (Map.sel bm e))
            (fun b -> exists_ (fun (bm_e':tid_bitmap) ->
                                      fpost (Map.sel bm e) bm_e' b
                                      `star`
                                      array_pts_to a bm_e'))
      = admit__()
    in
    let res = IArray.with_key tid_bitmaps e #bool #emp #fpost f in
    match res with
    | EHT.Present b ->
      rewrite (IArray.with_key_post bm tid_bitmaps e emp fpost res)
              (IArray.with_key_post bm tid_bitmaps e emp fpost (EHT.Present b));
      let bm_e' = IArray.elim_with_key_post_present b in
      assert_ (fpost (Map.sel bm e) (reveal bm_e') b);
      rewrite (fpost (Map.sel bm e) (reveal bm_e') b)
              (pure (Map.sel bm e == reveal bm_e' /\
                     (b ==> Map.sel bm e == all_ones)));
      elim_pure _;
      assert (Map.upd bm e (Map.sel bm e) `Map.equal` bm);
      rewrite (IArray.perm tid_bitmaps (Map.upd bm e (Map.sel bm e)))
              (IArray.perm tid_bitmaps bm);
      return b
    | _ ->
      rewrite (IArray.with_key_post bm tid_bitmaps e emp fpost res)
              (IArray.perm tid_bitmaps bm `star` emp);
      return false

let check_hash_equality_for_epoch (#hashes_v:erased (IArray.repr M.epoch_id M.epoch_hash))
                                  (hashes:all_epoch_hashes)
                                  (e:M.epoch_id)
  : ST bool
    (IArray.perm hashes hashes_v)
    (fun _ -> IArray.perm hashes hashes_v)
    (requires True)
    (ensures fun b ->
      let ha = Map.sel hashes_v e in
      b ==> ha.hadd == ha.hevict)
  = let fpost (repr repr':M.epoch_hash) (b:bool) =
        pure (repr == repr' /\
             (b ==> repr'.hadd == repr'.hevict))
    in
    let f (ehs:epoch_hashes_t)
      : STT bool
        (emp `star` epoch_hash_perm e ehs (Map.sel hashes_v e))
        (fun b -> exists_ (fun (repr':M.epoch_hash) ->
                fpost (Map.sel hashes_v e) repr' b
                      `star`
                epoch_hash_perm e ehs repr'))
      = admit__()
    in
    let res = IArray.with_key hashes e #bool #emp #fpost f in
    match res with
    | EHT.Present b ->
      rewrite (IArray.with_key_post hashes_v hashes e emp fpost res)
              (IArray.with_key_post hashes_v hashes e emp fpost (EHT.Present b));
      let repr' = IArray.elim_with_key_post_present b in
      assert_ (fpost (Map.sel hashes_v e) (reveal repr') b);
      rewrite (fpost (Map.sel hashes_v e) (reveal repr') b)
              (pure (Map.sel hashes_v e == reveal repr' /\
                     (b ==> repr'.M.hadd == repr'.M.hevict)));
      elim_pure _;
      assert (Map.upd hashes_v e (Map.sel hashes_v e) `Map.equal` hashes_v);
      rewrite (IArray.perm hashes _)
              (IArray.perm hashes hashes_v);
      return b
    | _ ->
      rewrite (IArray.with_key_post hashes_v hashes e emp fpost res)
              (IArray.perm hashes hashes_v `star` emp);
      return false


let epoch_ready_if_bitmap_set (hashes:IArray.repr _ _)
                              (bitmaps:_)
                              (max:_)
                              (mlogs_v:_)
                              (e:M.epoch_id)
  : Lemma
    (requires
      hashes_bitmaps_max_ok hashes bitmaps max mlogs_v /\
      Map.sel bitmaps e == all_ones)
    (ensures
      epoch_is_complete mlogs_v e /\
      Map.sel hashes e == aggregate_all_threads_epoch_hashes e mlogs_v)
  = ()

let epoch_is_certified (mlogs_v:all_processed_entries)
                       (e:M.epoch_id)
  = let hashes = aggregate_all_threads_epoch_hashes e mlogs_v in
    epoch_is_complete mlogs_v e /\
    hashes.hadd == hashes.hevict

let max_is_correct (mlogs_v:_) (max:_)
  : prop
  = forall (e:M.epoch_id).
          U32.v e <= U32.v max ==>
          epoch_is_certified mlogs_v e

let _max_is_correct (hashes:_)
                    (bitmaps:_)
                    (max:_)
                    (mlogs_v:_)
  : Lemma
    (requires hashes_bitmaps_max_ok hashes bitmaps max mlogs_v)
    (ensures  max_is_correct mlogs_v max)
  = ()


let try_increment_max (#hashes_v:erased _)
                      (#bitmaps_v:erased _)
                      (#mlogs_v:erased _)
                      (hashes: all_epoch_hashes)
                      (bitmaps: epoch_tid_bitmaps)
                      (max:R.ref M.epoch_id)
  : STT bool
    (IArray.perm hashes hashes_v `star`
     IArray.perm bitmaps bitmaps_v `star`
     exists_ (fun max_v ->
       R.pts_to max full max_v `star`
       pure (hashes_bitmaps_max_ok hashes_v bitmaps_v max_v mlogs_v)))
    (fun b ->
      IArray.perm hashes hashes_v `star`
      IArray.perm bitmaps bitmaps_v `star`
      exists_ (fun (max_v':M.epoch_id) ->
        R.pts_to max full max_v' `star`
        pure (hashes_bitmaps_max_ok hashes_v bitmaps_v max_v' mlogs_v)))
  = let max_v = elim_exists () in
    let e = R.read max in
    let v = check_overflow_add32 e 1ul in
    match v with
    | None ->
      intro_exists_erased max_v (fun max_v' ->
        R.pts_to max full max_v' `star`
        pure (hashes_bitmaps_max_ok hashes_v bitmaps_v max_v' mlogs_v));
      return false

    | Some e' ->
      let ready = check_bitmap_for_epoch bitmaps e' in
      if not ready
      then (
        intro_exists_erased max_v (fun max_v' ->
          R.pts_to max full max_v' `star`
          pure (hashes_bitmaps_max_ok hashes_v bitmaps_v max_v' mlogs_v));
        return false
      )
      else (
        let b = check_hash_equality_for_epoch hashes e' in
        if not b
        then (
          intro_exists_erased max_v (fun max_v' ->
            R.pts_to max full max_v' `star`
            pure (hashes_bitmaps_max_ok hashes_v bitmaps_v max_v' mlogs_v));
          return false
        )
        else (
          R.write max e';
          elim_pure _;
          intro_pure (hashes_bitmaps_max_ok hashes_v bitmaps_v e' mlogs_v);
          intro_exists e' (fun max_v' ->
            R.pts_to max full max_v' `star`
            pure (hashes_bitmaps_max_ok hashes_v bitmaps_v max_v' mlogs_v));
          return true
        )
      )

let try_advance_max (#hashes_v:erased _)
                    (#bitmaps_v:erased _)
                    (#max_v:erased _)
                    (#mlogs_v:erased _)
                    (hashes: all_epoch_hashes)
                    (bitmaps: epoch_tid_bitmaps)
                    (max:R.ref M.epoch_id)
  : STT M.epoch_id
    (IArray.perm hashes hashes_v `star`
     IArray.perm bitmaps bitmaps_v `star`
     R.pts_to max full max_v `star`
     pure (hashes_bitmaps_max_ok hashes_v bitmaps_v max_v mlogs_v))
    (fun max_v' ->
      IArray.perm hashes hashes_v `star`
      IArray.perm bitmaps bitmaps_v `star`
      R.pts_to max full max_v' `star`
      pure (hashes_bitmaps_max_ok hashes_v bitmaps_v max_v' mlogs_v))
  = intro_exists_erased max_v (fun max_v ->
       R.pts_to max full max_v `star`
       pure (hashes_bitmaps_max_ok hashes_v bitmaps_v max_v mlogs_v));
    repeat_until _ (fun _ -> try_increment_max #hashes_v #bitmaps_v #mlogs_v hashes bitmaps max);
    let _ = elim_exists _ in
    let max = R.read max in
    elim_pure _;
    intro_pure _;
    return max

let release_lock (#hv:erased _)
                 (#bitmaps:erased _)
                 (#max:erased _)
                 (#mlogs_v:erased _)
                 (#hashes : all_epoch_hashes)
                 (#tid_bitmaps : epoch_tid_bitmaps)
                 (#max_certified_epoch : R.ref M.epoch_id)
                 (#mlogs: TLM.t)
                 (lock: cancellable_lock
                        (lock_inv hashes tid_bitmaps max_certified_epoch mlogs))
  : STT unit
    (lock_inv_body hashes tid_bitmaps max_certified_epoch mlogs
                       hv bitmaps max mlogs_v `star`
     can_release lock)
    (fun _ -> emp)
  = intro_exists_erased mlogs_v
      (fun mlogs_v ->  lock_inv_body hashes tid_bitmaps max_certified_epoch mlogs
                                      hv bitmaps max mlogs_v);
    intro_exists_erased max
      (fun max ->
        exists_ (fun mlogs_v ->
                    lock_inv_body hashes tid_bitmaps max_certified_epoch mlogs
                                      hv bitmaps max mlogs_v));
    intro_exists_erased bitmaps
      (fun bitmaps ->
        exists_ (fun max ->
        exists_ (fun mlogs_v ->
                    lock_inv_body hashes tid_bitmaps max_certified_epoch mlogs
                                      hv bitmaps max mlogs_v)));
    intro_exists_erased hv
      (fun hv ->
        exists_ (fun bitmaps ->
        exists_ (fun max ->
        exists_ (fun mlogs_v ->
                    lock_inv_body hashes tid_bitmaps max_certified_epoch mlogs
                                      hv bitmaps max mlogs_v))));
    release lock

let advance_and_read_max_certified_epoch (aeh:aggregate_epoch_hashes)
  : STT (option M.epoch_id)
      emp
      (fun max_opt ->
        match max_opt with
        | None -> emp //underspec: overflow or element went missing in IArray
        | Some max ->
          exists_ (fun logs ->
           TLM.global_snapshot aeh.mlogs (map_of_seq logs) `star`
           pure (max_is_correct logs max)))
  = let b = acquire aeh.lock in
    if not b
    then (
      rewrite (maybe_acquired _ _)
              emp;
      return None
    )
    else (
      rewrite (maybe_acquired _ _)
              (lock_inv aeh.hashes
                        aeh.tid_bitmaps
                        aeh.max_certified_epoch
                        aeh.mlogs `star`
              can_release aeh.lock);
      let _hv = elim_exists () in
      let _bitmaps = elim_exists () in
      let _max = elim_exists () in
      let _mlogs_v : erased all_processed_entries =
          elim_exists #_ #_
            #(lock_inv_body
                 aeh.hashes
                 aeh.tid_bitmaps
                 aeh.max_certified_epoch
                 aeh.mlogs
                 _hv
                 _bitmaps
                 _max)
            ()
      in

      let max = try_advance_max aeh.hashes aeh.tid_bitmaps aeh.max_certified_epoch in
      extract_pure _;

      intro_pure (max_is_correct _mlogs_v max);
      TLM.take_snapshot aeh.mlogs (map_of_seq _mlogs_v);
      intro_exists_erased _mlogs_v
        (fun logs ->
           TLM.global_snapshot aeh.mlogs (map_of_seq logs) `star`
           pure (max_is_correct logs max));
      release_lock #_ #_ #(hide max) aeh.lock;
      return (Some max)
    )
