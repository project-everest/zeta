module Zeta.Steel.Verifier
friend Zeta.Steel.VerifierTypes
open Zeta.Steel.VerifierTypes
open FStar.Ghost
open Steel.ST.Util
module G = Steel.ST.GhostReference
module R = Steel.ST.Reference
module A = Steel.ST.Array
module GMap = Zeta.Steel.GhostSharedMap
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

#push-options "--query_stats --fuel 0 --ifuel 1"

let set_add_remove (#a:eqtype) (s:Set.set a) (x:a)
  : Lemma (requires not (Set.mem x s))
          (ensures IArray.set_remove (IArray.set_add s x) x == s)
          [SMTPat (IArray.set_remove (IArray.set_add s x) x)]
  = let lhs = IArray.set_remove (IArray.set_add s x) x in
    Set.lemma_equal_intro lhs s;
    assert (lhs `Set.equal` s)

let map_upd_sel_eq (#k:eqtype) (#v:Type) (m:Map.t k v)
                   (x:k)
  : Lemma (requires Map.contains m x)
          (ensures Map.upd m x (Map.sel m x) == m)
          [SMTPat (Map.upd m x (Map.sel m x))]
  = assert (Map.upd m x (Map.sel m x) `Map.equal` m)

[@@__reduce__]
let thread_state_inv' (t:thread_state_t)
                      ([@@@smt_fallback] tsm:M.thread_state_model)
  : vprop
  = R.pts_to t.failed full tsm.failed `star`
    A.pts_to t.store tsm.store `star`
    R.pts_to t.clock full tsm.clock `star`
    IArray.perm t.epoch_hashes tsm.epoch_hashes Set.empty `star`
    R.pts_to t.last_verified_epoch full tsm.last_verified_epoch `star`
    G.pts_to t.processed_entries full tsm.processed_entries `star`
    G.pts_to t.app_results full tsm.app_results `star`
    exists_ (A.pts_to t.serialization_buffer)

let spec_verify_epoch (tsm:M.thread_state_model)
  = let tsm = M.verifyepoch tsm in
    if tsm.failed then tsm
    else { tsm with M.processed_entries = Seq.snoc tsm.processed_entries (VerifyEpoch())}

let verify_epoch_committed_entries (tsm:M.thread_state_model)
  : Lemma (M.committed_entries (spec_verify_epoch tsm) ==
           (spec_verify_epoch tsm).processed_entries)
          [SMTPat (M.committed_entries (spec_verify_epoch tsm))]
  = admit()

let aggregate_one_epoch_hash (source:epoch_hashes_repr)
                             (dest:AEH.epoch_hashes_repr)
                             (e:M.epoch_id)
  : AEH.epoch_hashes_repr
  = Map.upd dest e (AEH.aggregate_epoch_hash
                      (Map.sel dest e)
                      (Map.sel source e))
let update_if (b:bool) (default_ upd_: 'a)
  : 'a
  = if b then upd_ else default_

let aggregate_epoch_hashes_t (#e:_)
                             (#s #d:M.epoch_hash)
                             (src:epoch_hashes_t)
                             (dst:AEH.epoch_hashes_t)
  : STT bool
    (epoch_hash_perm e src s `star`
     AEH.epoch_hash_perm e dst d)
    (fun b ->
      epoch_hash_perm e src s `star`
      AEH.epoch_hash_perm e dst (update_if b d (AEH.aggregate_epoch_hash d s)))
  = admit__() // need a utility from HA

let with_value_of_key (#k:eqtype)
                      (#v:Type0)
                      (#contents:Type0)
                      (#h:IArray.hash_fn k)
                      (#vp: k -> v -> contents -> vprop)
                      (#m:erased (IArray.repr k contents))
                      (#cf:contents -> GTot contents)
                      (t:IArray.tbl h vp)
                      (i:k)
                      ($f: (value:v -> STT v
                                         (vp i value (Map.sel m i))
                                         (fun value' -> vp i value' (cf (Map.sel m i)))))
  : STT bool
    (IArray.perm t m Set.empty)
    (fun b -> IArray.perm t (update_if b (reveal m) (Map.upd m i (cf (Map.sel m i)))) Set.empty)
  = let vopt = IArray.get t i in
    match vopt with
    | None ->
      rewrite (IArray.get_post _ _ _ _ _)
              (IArray.perm t m Set.empty);
      return false
    | Some value ->
      rewrite (IArray.get_post _ _ _ _ _)
              (vp i value (Map.sel m i) `star`
               IArray.perm t m (IArray.set_add Set.empty i));
      let value' = f value in
      IArray.put t i value' _;
      return true


let propagate_epoch_hash (#tsm:M.thread_state_model)
                         (t:thread_state_t)
                         (#hv:erased AEH.epoch_hashes_repr)
                         (hashes : AEH.all_epoch_hashes)
                         (e:M.epoch_id)
  : STT bool
    (thread_state_inv' t (M.verifyepoch tsm) `star`
     IArray.perm hashes hv Set.empty)
    (fun b ->
      thread_state_inv' t (M.verifyepoch tsm) `star`
      IArray.perm hashes (update_if b (reveal hv)
                                      (aggregate_one_epoch_hash (spec_verify_epoch tsm).epoch_hashes hv e))
                         Set.empty)
  = let dst = IArray.get hashes e in
    match dst with
    | None -> //we should distinguish Absent from Missing
      rewrite (IArray.get_post _ _ _ _ _)
              (IArray.perm hashes hv Set.empty);
      return false
    | Some dst ->
      rewrite (IArray.get_post _ _ _ _ _)
              (AEH.epoch_hash_perm e dst (Map.sel hv e) `star`
               IArray.perm hashes hv (IArray.set_add Set.empty e));
      let src = IArray.get t.epoch_hashes e in
      match src with
      | None ->
        rewrite (IArray.get_post _ _ t.epoch_hashes _ _)
                (IArray.perm t.epoch_hashes (M.verifyepoch tsm).epoch_hashes Set.empty);
        IArray.put hashes e dst _; //this should be a ghost put
        return false

      | Some src ->
        rewrite (IArray.get_post _ _ _ _ _)
                (epoch_hash_perm e src (Map.sel (M.verifyepoch tsm).epoch_hashes e) `star`
                 IArray.perm t.epoch_hashes (M.verifyepoch tsm).epoch_hashes (IArray.set_add Set.empty e));
        let b = aggregate_epoch_hashes_t src dst in
        IArray.put t.epoch_hashes e src _; //this should be a ghost put
        IArray.put hashes e dst _;
        return b


let update_bitmap_spec (bm:IArray.repr M.epoch_id AEH.tid_bitmap)
                       (e:M.epoch_id)
                       (tid:tid)
  : IArray.repr M.epoch_id AEH.tid_bitmap
  = Map.upd bm e (Seq.upd (Map.sel bm e) (U16.v tid) true)

let update_bitmap (#bm:erased _)
                  (tid_bitmaps: AEH.epoch_tid_bitmaps)
                  (e:M.epoch_id)
                  (tid:tid)
  : STT bool
    (IArray.perm tid_bitmaps bm Set.empty)
    (fun b ->
      IArray.perm tid_bitmaps
                  (update_if b
                             (reveal bm)
                             (update_bitmap_spec bm e tid))
                  Set.empty)
  = let update_tid (v:larray bool n_threads)
      : STT (larray bool n_threads)
        (A.pts_to v (Map.sel bm e))
        (fun v' -> A.pts_to v' (Seq.upd (Map.sel bm e) (U16.v tid) true))
      = A.write v (as_u32 tid) true;
        v
    in
    with_value_of_key tid_bitmaps e update_tid

let update_contributions_spec  (mlogs_v:AEH.all_processed_entries)
                               (tsm:M.thread_state_model)
  : GTot AEH.all_processed_entries
  = Seq.upd mlogs_v (U16.v tsm.thread_id) tsm.processed_entries

let update_logs_of_tid
         (mlogs_v:AEH.all_processed_entries)
         (tsm:M.thread_state_model)
  : GTot AEH.all_processed_entries
  = Seq.upd mlogs_v (U16.v tsm.thread_id) tsm.processed_entries

let map_of_seq_update_lemma  (mlogs_v:AEH.all_processed_entries)
                             (tsm:M.thread_state_model)
  : Lemma (Map.equal (Map.upd (AEH.map_of_seq mlogs_v) tsm.thread_id
                              (spec_verify_epoch tsm).processed_entries)
                     (AEH.map_of_seq (update_logs_of_tid mlogs_v (spec_verify_epoch tsm))))
  = admit()


let commit_entries #o
                   (#tsm:M.thread_state_model)
                   (#mlogs_v:AEH.all_processed_entries)
                   (t:thread_state_t)
                   (mylogref:AEH.monotonic_logs)
  : STGhost unit o
     (GMap.owns_key mylogref t.thread_id full tsm.processed_entries `star`
      GMap.global_snapshot mylogref (AEH.map_of_seq mlogs_v) `star`
      G.pts_to t.processed_entries full (M.verifyepoch tsm).processed_entries)
     (fun _ ->
      GMap.owns_key mylogref t.thread_id full (spec_verify_epoch tsm).processed_entries `star`
      GMap.global_snapshot mylogref (AEH.map_of_seq (update_logs_of_tid mlogs_v (spec_verify_epoch tsm))) `star`
      G.pts_to t.processed_entries full (spec_verify_epoch tsm).processed_entries)
     (requires t.thread_id == tsm.thread_id)
     (ensures fun _ -> True)
  = GMap.update mylogref (spec_verify_epoch tsm).processed_entries;
    GMap.update_global_snapshot mylogref (AEH.map_of_seq mlogs_v);
    G.write t.processed_entries (spec_verify_epoch tsm).processed_entries;
    map_of_seq_update_lemma mlogs_v tsm;
    rewrite
          (GMap.global_snapshot mylogref (Map.upd (AEH.map_of_seq mlogs_v) t.thread_id
                                                  (spec_verify_epoch tsm).processed_entries))
          (GMap.global_snapshot mylogref (AEH.map_of_seq (update_logs_of_tid mlogs_v (spec_verify_epoch tsm))))


let advance_per_thread_max_and_bitmap  (bitmaps:IArray.repr M.epoch_id AEH.tid_bitmap)
                                        (max:_)
                                        (mlogs_v:_)
                                        (tsm:M.thread_state_model)
                                        (e:M.epoch_id)
  : Lemma
    (requires (
      let tsm' = spec_verify_epoch tsm in
      AEH.per_thread_max_and_bitmap max bitmaps tsm.thread_id mlogs_v /\
      tsm'.last_verified_epoch == e))
    (ensures (
      let tsm' = spec_verify_epoch tsm in
      AEH.per_thread_max_and_bitmap
        max
        (update_bitmap_spec bitmaps e tsm.thread_id)
        tsm.thread_id
        (update_logs_of_tid mlogs_v tsm')))
  = admit()
    // let tsm0 = M.verify_model (M.init_thread_state_model tsm.thread_id) (M.committed_entries tsm) in
    // let tsm' = spec_verify_epoch tsm in
    // assume (tsm' == M.verify_model (M.init_thread_state_model tsm'.thread_id) tsm'.processed_entries); //from top-level inv
    // assume (U32.v e == U32.v tsm0.last_verified_epoch + 1); //from trace property
    // let tid = U16.v tsm.thread_id in
    // let contribs' = AEH.thread_contribs (update_contributions_spec tsm contribs e) tsm.thread_id in
    // let contribs = AEH.thread_contribs contribs tsm.thread_id in
    // let bitmaps' = update_bitmap_spec bitmaps e tsm.thread_id in
    // introduce
    //   forall (eid:M.epoch_id).
    //     let h_contrib = Map.sel contribs' eid in
    //     let h_tsm = Map.sel tsm'.epoch_hashes eid in
    //     Seq.index (Map.sel bitmaps' eid) (U16.v tsm'.thread_id) == AEH.is_epoch_verified eid tsm'.last_verified_epoch /\
    //     (if AEH.is_epoch_verified eid tsm'.last_verified_epoch
    //     then h_contrib == h_tsm
    //     else h_contrib == M.init_epoch_hash)
    // with (let h_contrib = Map.sel contribs' eid in
    //       let h_tsm = Map.sel tsm'.epoch_hashes eid in
    //       if eid <> e
    //       then (
    //         assert (Seq.index (Map.sel bitmaps eid) tid == Seq.index (Map.sel bitmaps' eid) tid);
    //         assert (U32.v eid < U32.v e ==> AEH.is_epoch_verified eid tsm'.last_verified_epoch);
    //         assert (AEH.is_epoch_verified eid tsm0.last_verified_epoch == AEH.is_epoch_verified eid tsm'.last_verified_epoch);
    //         assert (Seq.index (Map.sel bitmaps' eid) tid == AEH.is_epoch_verified eid tsm'.last_verified_epoch);
    //         if AEH.is_epoch_verified eid tsm0.last_verified_epoch
    //         then (
    //           assert (Map.sel contribs eid == h_contrib);
    //           assume (Map.sel tsm0.epoch_hashes eid == h_tsm); //hashes of verified epochs don't change
    //           assert (h_contrib == h_tsm)
    //         )
    //         else (
    //           assert (h_contrib == M.init_epoch_hash)
    //         )
    //       ))

let restore_per_thread_invariant #o
                                 (#bitmaps:IArray.repr M.epoch_id AEH.tid_bitmap)
                                 (#max:_)
                                 (#mlogs_v:_)
                                 (tsm:M.thread_state_model)
                                 (e:M.epoch_id {   tsm_entries_invariant tsm /\
                                                   (spec_verify_epoch tsm).last_verified_epoch == e } )
  : STGhostT unit o
    (AEH.per_thread_invariant max bitmaps mlogs_v tsm.thread_id)
    (fun _ ->
      let tsm' = spec_verify_epoch tsm in
      AEH.per_thread_invariant max (update_bitmap_spec bitmaps e tsm'.thread_id)
                                   (update_logs_of_tid mlogs_v tsm')
                                   tsm'.thread_id)
  = elim_pure _;
    advance_per_thread_max_and_bitmap bitmaps max mlogs_v tsm e;
    intro_pure _

let restore_other_threads_invariant #o
                                 (#bitmaps:IArray.repr M.epoch_id AEH.tid_bitmap)
                                 (#max:_)
                                 (#mlogs_v:_)
                                 (tsm:M.thread_state_model)
                                 (e:M.epoch_id)
                                 (t':AEH.refined_tid (fun t' -> tsm.thread_id <> t'))

  : STGhostT unit o
    (AEH.per_thread_invariant max bitmaps mlogs_v t')
    (fun _ -> AEH.per_thread_invariant max (update_bitmap_spec bitmaps e tsm.thread_id)
                                        (update_logs_of_tid mlogs_v tsm)
                                        t')
  = // let _entries = elim_exists () in
    elim_pure _;
    intro_pure (AEH.per_thread_max_and_bitmap max
                                              (update_bitmap_spec bitmaps e tsm.thread_id)
                                              t'
                                              (update_logs_of_tid mlogs_v tsm))

[@@__reduce__]
let forall_threads_except (i:tid) (p:tid -> vprop) =
     AEH.forall_threads_between 0us i p `star`
     AEH.forall_threads_between U16.(i +^ 1us) AEH.n_threads_16 p

let restore_all_threads_invariant #o
                                 (#bitmaps:IArray.repr M.epoch_id AEH.tid_bitmap)
                                 (#max:_)
                                 (#mlogs_v:_)
                                 (#t:tid)
                                 (tsm:M.thread_state_model)
                                 (e:M.epoch_id)
 : STGhost unit o
   (AEH.per_thread_invariant max (update_bitmap_spec bitmaps e tsm.thread_id)
                                 (update_logs_of_tid mlogs_v tsm)
                                 tsm.thread_id `star`
    forall_threads_except t (AEH.per_thread_invariant max bitmaps mlogs_v))
   (fun _ ->
    AEH.forall_threads (AEH.per_thread_invariant max (update_bitmap_spec bitmaps e tsm.thread_id)
                                                     (update_logs_of_tid mlogs_v tsm)))
   (requires t == tsm.thread_id)
   (ensures fun _ -> True)
 = rewrite (forall_threads_except t (AEH.per_thread_invariant max bitmaps mlogs_v))
           (forall_threads_except tsm.thread_id (AEH.per_thread_invariant max bitmaps mlogs_v));
   AEH.update_forall_thread_between
    #o
    #(AEH.per_thread_invariant max bitmaps mlogs_v)
    #(AEH.per_thread_invariant max (update_bitmap_spec bitmaps e tsm.thread_id)
                                   (update_logs_of_tid mlogs_v tsm))
    0us tsm.thread_id
    (restore_other_threads_invariant tsm e);
   AEH.update_forall_thread_between
    #o
    #(AEH.per_thread_invariant max bitmaps mlogs_v)
    #(AEH.per_thread_invariant max (update_bitmap_spec bitmaps e tsm.thread_id)
                                   (update_logs_of_tid mlogs_v tsm))
    _ _
    (restore_other_threads_invariant tsm e);
    AEH.put_thread tsm.thread_id

let restore_all_threads_invariant' #o
                                 (#bitmaps:IArray.repr M.epoch_id AEH.tid_bitmap)
                                 (#max:M.epoch_id)
                                 (#mlogs_v:AEH.all_processed_entries)
                                 (tsm:M.thread_state_model)
                                 (e:M.epoch_id)
  : STGhost unit o
    (AEH.forall_threads (AEH.per_thread_invariant max bitmaps mlogs_v))
    (fun _ ->
      AEH.forall_threads (AEH.per_thread_invariant max (update_bitmap_spec bitmaps e (spec_verify_epoch tsm).thread_id)
                                                       (update_logs_of_tid mlogs_v (spec_verify_epoch tsm))))
    (requires
       tsm_entries_invariant tsm /\
       (spec_verify_epoch tsm).last_verified_epoch == e)
    (ensures fun _ -> True)
  = let _ = AEH.take_thread tsm.thread_id in
    restore_per_thread_invariant tsm e;
    restore_all_threads_invariant #o #bitmaps #max #mlogs_v #tsm.thread_id (spec_verify_epoch tsm) e

let restore_global_invariant #o #hv #bm #max #mlogs_v (tsm:M.thread_state_model) (e:M.epoch_id)
  : STGhostT unit o
    (pure (AEH.contribs_and_max_ok hv bm max mlogs_v))
    (fun _ ->
      pure (AEH.contribs_and_max_ok
                        (aggregate_one_epoch_hash tsm.epoch_hashes hv e)
                        (update_bitmap_spec bm e tsm.thread_id)
                        max
                        (update_logs_of_tid mlogs_v tsm)))
  = let hv' = aggregate_one_epoch_hash tsm.epoch_hashes hv e in
    let mlogs_v' = update_logs_of_tid mlogs_v tsm in
    let bm' = update_bitmap_spec bm e tsm.thread_id in
    assume (U32.v max < U32.v e );
    let aux1 ()
      : Lemma
        (requires
          AEH.all_contributions_are_accurate hv mlogs_v)
        (ensures
          AEH.all_contributions_are_accurate hv' mlogs_v')
      = admit()
        // introduce
        //   forall (e':M.epoch_id).
        //     Map.sel hv' e' == AEH.aggregate_thread_epoch_hashes e' cv'
        // with (
        //   if e' <> e
        //   then (
        //     calc (==) {
        //        AEH.aggregate_thread_epoch_hashes e' cv';
        //        == { AEH.frame_aggregate_thread_epoch_hashes e' e cv tsm.thread_id (Map.sel tsm.epoch_hashes e) }
        //        AEH.aggregate_thread_epoch_hashes e' cv;
        //     }
        //   )
        //   else (
        //     calc (==) {
        //       AEH.aggregate_thread_epoch_hashes e cv';
        //       (==) { }
        //       Zeta.SeqAux.reduce M.init_epoch_hash
        //                (fun s -> AEH.aggregate_epoch_hash (Map.sel s e))
        //                cv';
        //       (==) {admit()} //probably easier to do this using the permutation monoid
        //                      //and we need to know that the bit for tsm was false initially
        //       AEH.aggregate_epoch_hash (AEH.aggregate_thread_epoch_hashes e cv)
        //                                (Map.sel tsm.epoch_hashes e);
        //     }
        //   )
        // )
    in
    elim_pure _;
    aux1 ();
    intro_pure _


let intro_thread_state_inv #o
                           (tsm:M.thread_state_model)
                           (#f:_)
                           (#s:_)
                           (#c:_)
                           (#eh:_)
                           (#lve:_)
                           (#pe:_)
                           (#ar:_)
                           (t:thread_state_t)
   : STGhost unit o
     (R.pts_to t.failed full f `star`
      A.pts_to t.store s `star`
      R.pts_to t.clock full c `star`
      IArray.perm t.epoch_hashes eh Set.empty `star`
      R.pts_to t.last_verified_epoch full lve `star`
      G.pts_to t.processed_entries full pe `star`
      G.pts_to t.app_results full ar `star`
      exists_ (A.pts_to t.serialization_buffer))
     (fun _ -> thread_state_inv' t tsm)
     (requires
       tsm.failed == f /\
       tsm.store == s /\
       tsm.clock == c /\
       tsm.epoch_hashes == eh /\
       tsm.last_verified_epoch == lve /\
       tsm.processed_entries == pe /\
       tsm.app_results == ar)
     (ensures fun _ ->
       True)
   = rewrite (R.pts_to t.failed _ _ `star`
              A.pts_to t.store _ `star`
              R.pts_to t.clock _ _ `star`
              IArray.perm t.epoch_hashes _ _ `star`
              R.pts_to t.last_verified_epoch _ _ `star`
              G.pts_to t.processed_entries _ _ `star`
              G.pts_to t.app_results _ _ `star`
              exists_ (A.pts_to t.serialization_buffer))
             (thread_state_inv' t tsm)

#push-options "--query_stats"

let verify_epoch (#tsm:M.thread_state_model)
                 (t:thread_state_t)
                 (hashes : AEH.all_epoch_hashes)
                 (tid_bitmaps : AEH.epoch_tid_bitmaps)
                 (max_certified_epoch : R.ref M.epoch_id)
                 (mlogs: AEH.monotonic_logs)
                 (lock: cancellable_lock (AEH.lock_inv hashes tid_bitmaps max_certified_epoch mlogs))
  : ST bool
    (thread_state_inv' t tsm `star`
     GMap.owns_key mlogs t.thread_id full tsm.processed_entries)
    (fun b ->
      thread_state_inv' t (update_if b (M.verifyepoch tsm)
                                       (spec_verify_epoch tsm)) `star`
      GMap.owns_key mlogs t.thread_id full (update_if b tsm.processed_entries
                                                           (spec_verify_epoch tsm).processed_entries))
    (requires
      t.thread_id == tsm.thread_id /\
      tsm_entries_invariant tsm)
    (ensures fun _ -> True)
  = let e = R.read t.last_verified_epoch in
    let e' = st_check_overflow_add32 e 1ul in
    match e' with
    | None ->
      R.write t.failed true; return true

    | Some e ->
      R.write t.last_verified_epoch e;
      assert_ (thread_state_inv' t (M.verifyepoch tsm));

      assert ((spec_verify_epoch tsm).last_verified_epoch == e);

      let acquired = acquire lock in
      if not acquired
      then (
        rewrite (maybe_acquired _ _)
                emp;
        return false
      )
      else (
        rewrite (maybe_acquired _ _)
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

        let b0 = propagate_epoch_hash t hashes e in
        let b1 = update_bitmap tid_bitmaps e t.thread_id in
        if not b0 || not b1
        then ( //propagation failed, e.g., due to overflow
           cancel lock;
           drop _; //drop resources protected by lock; invariant is lost
           return false
        )
        else (
             commit_entries t mlogs;
             restore_all_threads_invariant' tsm e;
             restore_global_invariant (spec_verify_epoch tsm) e;
             release_lock  #hashes #tid_bitmaps #max_certified_epoch #mlogs
                           #(hide (aggregate_one_epoch_hash (spec_verify_epoch tsm).epoch_hashes _hv e))
                           #(hide (update_bitmap_spec _bitmaps e (spec_verify_epoch tsm).thread_id))
                           #_max
                           lock;
             return true
        )
      )

#push-options "--print_implicits"

let spec_parser_log  = admit()

let finalize_epoch_hash
  : IArray.finalizer epoch_hash_perm
  = fun k v -> drop _ //TODO: Actually free it

#push-options "--fuel 1"
let create (tid:tid)
  : STT thread_state_t
    emp
    (fun t -> thread_state_inv t (M.init_thread_state_model tid))
  = let failed = R.alloc false in
    let store : vstore = A.alloc None (as_u32 store_size) in
    let clock = R.alloc 0uL in
    let epoch_hashes = IArray.create epoch_id_hash 64ul finalize_epoch_hash in
    let last_verified_epoch = R.alloc 0ul in
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
        last_verified_epoch;
        processed_entries;
        app_results;
        serialization_buffer
    } in
    intro_exists _ (A.pts_to serialization_buffer);
    assert (tsm == M.verify_model tsm Seq.empty);
    intro_pure (tsm == M.verify_model tsm Seq.empty);
    rewrite (R.pts_to failed _ _ `star`
             A.pts_to store _ `star`
             R.pts_to clock _ _ `star`
             IArray.perm epoch_hashes _ _ `star`
             R.pts_to last_verified_epoch _ _ `star`
             G.pts_to processed_entries _ _ `star`
             G.pts_to app_results _ _ `star`
             exists_ (A.pts_to serialization_buffer) `star`
             pure (tsm == M.verify_model tsm Seq.empty)
            )
            (thread_state_inv t (M.init_thread_state_model tid));
    return t
#pop-options

////////////////////////////////////////////////////////////////////////////////
// Just a couple of warm ups, we don't actually need this
////////////////////////////////////////////////////////////////////////////////

let tsm_t (tsm:M.thread_state_model) =
    t:thread_state_t { t.thread_id == tsm.thread_id}



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
              (epoch_hash_perm e v (Map.sel tsm.epoch_hashes e) `star`
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
                             epoch_hash_perm e v
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


let new_epoch (e:M.epoch_id)
  : STT epoch_hashes_t
    emp
    (fun v -> epoch_hash_perm e v M.init_epoch_hash)
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
           (#logrefs: AEH.log_refs_t)
           (aeh:AEH.aggregate_epoch_hashes logrefs) //lock & handle to the aggregate state
           (mylogref:AEH.log_ref { //this thread's contribution to the aggregate state
             Map.sel logrefs tsm.thread_id == mylogref
            })
  = admit__()
