module Zeta.Steel.Verifier
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
module P = Zeta.Steel.Parser
module Cast = FStar.Int.Cast

let as_u32 (s:U16.t) : U32.t = Cast.uint16_to_uint32 s
#push-options "--ide_id_info_off"

#push-options "--query_stats --fuel 0 --ifuel 1"

////////////////////////////////////////////////////////////////////////////////
// Some utilities
////////////////////////////////////////////////////////////////////////////////
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

/// Many functions have specs using update_if
///  -- they conditionally update the state leaving it unchanged in case of failure
let update_if (b:bool) (default_ upd_: 'a)
  : 'a
  = if b then upd_ else default_

////////////////////////////////////////////////////////////////////////////////
//We'll mostly work with thread_state_inv'
//which is similar to thread_state_inv without its pure parts
//The full thread_state_inv, with the pure parts is handled mainly
//at the top level verify call at the end of this fail
////////////////////////////////////////////////////////////////////////////////
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

let intro_thread_state_inv' #o
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

////////////////////////////////////////////////////////////////////////////////
//verify_epoch: One of the most delicate functions in the API is
//verify_epoch, since it involves working with the aggregate epoch state
//We implement that first, with several auxiliary lemmas and helper functions
////////////////////////////////////////////////////////////////////////////////
let spec_verify_epoch (tsm:M.thread_state_model)
  = let tsm = M.verifyepoch tsm in
    if tsm.failed then tsm
    else { tsm with M.processed_entries = Seq.snoc tsm.processed_entries (VerifyEpoch())}

let verify_epoch_committed_entries (tsm:M.thread_state_model)
  : Lemma (M.committed_entries (spec_verify_epoch tsm) ==
           (spec_verify_epoch tsm).processed_entries)
          [SMTPat (M.committed_entries (spec_verify_epoch tsm))]
  = admit() //should be an easy lemma about sequence prefixes

let aggregate_one_epoch_hash (source:epoch_hashes_repr)
                             (dest:AEH.epoch_hashes_repr)
                             (e:M.epoch_id)
  : AEH.epoch_hashes_repr
  = Map.upd dest e (AEH.aggregate_epoch_hash
                      (Map.sel dest e)
                      (Map.sel source e))

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

/// A utility, should be replaced by a similar function in EphemeralHashtbl
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


/// Updates the aggregate epoch hash for a thread with the
/// t thread-local epoch hashes for epoch e
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

/// Update the bitmap for tid indicating that it's epoch contribution
/// is ready
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
     (requires t.thread_id == tsm.thread_id)
     (ensures fun _ -> True)
  = TLM.take_anchor_tid mylogref _ _ _ _;
    verify_epoch_committed_entries tsm;
    TLM.update_anchored_tid_log mylogref _ _ (spec_verify_epoch tsm).processed_entries;
    TLM.put_anchor_tid mylogref _ _ _ _;
    G.write t.processed_entries (spec_verify_epoch tsm).processed_entries;
    map_of_seq_update_lemma mlogs_v tsm;
    rewrite
          (TLM.global_anchor mylogref _)
          (TLM.global_anchor mylogref (AEH.map_of_seq (update_logs_of_tid mlogs_v (spec_verify_epoch tsm))))

let spec_verify_epoch_entries_invariants (tsm:M.thread_state_model)
  : Lemma
    (requires (tsm_entries_invariant tsm))
    (ensures (tsm_entries_invariant (spec_verify_epoch tsm)))
  = admit()

let last_verified_epoch_constant (tsm:M.thread_state_model)
  : Lemma
    (requires
      tsm_entries_invariant tsm)
    (ensures (
      let tsm0 = M.verify_model (M.init_thread_state_model tsm.thread_id) (M.committed_entries tsm) in
      tsm.last_verified_epoch == tsm0.last_verified_epoch))
  = admit() //the last_verified_epoch only changed when processing a verify_epoch entry

#push-options "--query_stats"
let advance_per_thread_bitmap_and_max  (bitmaps:IArray.repr M.epoch_id AEH.tid_bitmap)
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
    last_verified_epoch_constant tsm;
    assert (tsm0.last_verified_epoch == tsm.last_verified_epoch);
    let tsm' = spec_verify_epoch tsm in
    let bitmaps' = update_bitmap_spec bitmaps e tsm.thread_id in
    let logs' = update_logs_of_tid mlogs_v tsm' in
    spec_verify_epoch_entries_invariants tsm;
    assert (U32.v max <= U32.v tsm0.last_verified_epoch);
    assert (U32.v e == U32.v tsm.last_verified_epoch + 1);
    assert (U32.v max <= U32.v tsm'.last_verified_epoch)

let restore_all_threads_bitmap_and_max  (bitmaps:IArray.repr M.epoch_id AEH.tid_bitmap)
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

let lemma_restore_hashes_bitmaps_max_ok
                                  (hashes:epoch_hashes_repr)
                                  (bitmaps: IArray.repr M.epoch_id AEH.tid_bitmap)
                                  (max:M.epoch_id)
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
         (==) { _ by (FStar.Tactics.trefl()) }
         Zeta.SeqAux.reduce M.init_epoch_hash
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
    assert (U32.v max <= U32.v tsm0.last_verified_epoch);
    last_verified_epoch_constant tsm

let restore_hashes_bitmaps_max_ok (#o:_)
                                  (#hashes:epoch_hashes_repr)
                                  (#bitmaps: IArray.repr M.epoch_id AEH.tid_bitmap)
                                  (#max:M.epoch_id)
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

#push-options "--query_stats"

////////////////////////////////////////////////////////////////////////////////
// Finally verify_epoch itself
////////////////////////////////////////////////////////////////////////////////
let verify_epoch (#tsm:M.thread_state_model)
                 (t:thread_state_t)
                 (hashes : AEH.all_epoch_hashes)
                 (tid_bitmaps : AEH.epoch_tid_bitmaps)
                 (max_certified_epoch : R.ref M.epoch_id)
                 (mlogs: TLM.t)
                 (lock: cancellable_lock (AEH.lock_inv hashes tid_bitmaps max_certified_epoch mlogs))
  : ST bool
    (thread_state_inv' t tsm `star`
     TLM.tid_pts_to mlogs t.thread_id full tsm.processed_entries false)
    (fun b ->
      thread_state_inv' t (update_if b (M.verifyepoch tsm)
                                       (spec_verify_epoch tsm)) `star`
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
             commit_entries t mlogs;
             restore_hashes_bitmaps_max_ok tsm e;
             AEH.release_lock #(hide (aggregate_one_epoch_hash (spec_verify_epoch tsm).epoch_hashes _hv e))
                              #(hide (update_bitmap_spec _bitmaps e (spec_verify_epoch tsm).thread_id))
                              lock;
             return true
        )
      )

////////////////////////////////////////////////////////////////////////////////

let spec_parser_log  = admit()

let finalize_epoch_hash
  : IArray.finalizer epoch_hash_perm
  = fun k v -> drop _ //TODO: Actually free it

////////////////////////////////////////////////////////////////////////////////
// create a thread
////////////////////////////////////////////////////////////////////////////////
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
    intro_pure (tsm_entries_invariant (M.init_thread_state_model tid) /\
                t.thread_id == tsm.thread_id);
    rewrite (R.pts_to failed _ _ `star`
             A.pts_to store _ `star`
             R.pts_to clock _ _ `star`
             IArray.perm epoch_hashes _ _ `star`
             R.pts_to last_verified_epoch _ _ `star`
             G.pts_to processed_entries _ _ `star`
             G.pts_to app_results _ _ `star`
             exists_ (A.pts_to serialization_buffer) `star`
             pure (tsm_entries_invariant (M.init_thread_state_model tid) /\
                   t.thread_id == tsm.thread_id)
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

////////////////////////////////////////////////////////////////////////////////
//vget: We don't use this anymore, but it's a short function to check
//      that things verify as expected
////////////////////////////////////////////////////////////////////////////////
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

////////////////////////////////////////////////////////////////////////////////
//vput: We don't use this anymore, but it's a short function to check
//      that things verify as expected
////////////////////////////////////////////////////////////////////////////////
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

////////////////////////////////////////////////////////////////////////////////
//vevictm
////////////////////////////////////////////////////////////////////////////////
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

////////////////////////////////////////////////////////////////////////////////
// Some utilities for vevictb and vevictbm
////////////////////////////////////////////////////////////////////////////////
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

let ha_add (#v:erased (HA.hash_value_t))
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
  = admit__()

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
       return b
     )
     else (
       rewrite (thread_state_inv' t _) (thread_state_inv' t tsm);
       return b
     )

////////////////////////////////////////////////////////////////////////////////
//vevictb
////////////////////////////////////////////////////////////////////////////////
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
    intro_thread_state_inv' (update_if b tsm tsm') t;
    return b

////////////////////////////////////////////////////////////////////////////////
//vevictbm: A bit delicate. TODO should debug the SMT queries.
////////////////////////////////////////////////////////////////////////////////
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


////////////////////////////////////////////////////////////////////////////////
// nextepoch
////////////////////////////////////////////////////////////////////////////////
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


////////////////////////////////////////////////////////////////////////////////
//vaddb
////////////////////////////////////////////////////////////////////////////////
let record = (k:key & v:T.value{ M.is_value_of k v })

let next (t:T.timestamp)
  : option T.timestamp
  = if FStar.UInt.fits (U64.v t + 1) 64
    then Some (U64.add t 1uL)
    else None

let max (t0 t1:T.timestamp)
  = let open U64 in
    if t0 >=^ t1 then t0 else t1

let vaddb (#tsm:M.thread_state_model)
          (t:thread_state_t)
          (s:slot_id)
          (ts:timestamp)
          (thread_id:T.thread_id)
          (p:erased M.payload)
          (r:T.record)
  : ST bool
       (thread_state_inv' t tsm)
       (fun b -> thread_state_inv' t (update_if b tsm (M.vaddb tsm s ts thread_id p)))
       (requires Some r == M.record_of_payload p)
       (ensures fun _ -> True)
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
             rewrite (thread_state_inv' t _)
                     (thread_state_inv' t (update_epoch_hash tsm (M.epoch_of_timestamp ts) r ts thread_id HAdd));
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
            rewrite (thread_state_inv' t _) (thread_state_inv' t tsm);
            return ok
          )
        )
      )
    )

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
    (thread_state_inv' t tsm)
    (fun _ -> thread_state_inv' t (M.madd_to_store_split tsm s k v s' d d2))
  = let b = (M.is_value_of k v) in
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
    (thread_state_inv' t tsm)
    (fun _ -> thread_state_inv' t (M.madd_to_store tsm s k v s' d))
  = let b = (M.is_value_of k v) in
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

let vaddm (#tsm:M.thread_state_model)
          (t:thread_state_t)
          (s s':slot_id)
          (p:erased M.payload)
          (r:T.record)
  : ST bool
    (thread_state_inv' t tsm)
    (fun b -> thread_state_inv' t (update_if b tsm (M.vaddm tsm s s' p)))
    (requires Some r == M.record_of_payload p)
    (ensures fun _ -> True)
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
                          (thread_state_inv' t tsm)
                          (fun b -> thread_state_inv' t (update_if b tsm (M.vaddm tsm s s' p))))
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
                         assert_ (thread_state_inv' t (M.vaddm tsm s s' p));
                         let b = true in
//                         intro_thread_state_inv' (update_if b tsm (M.vaddm tsm s s' p)) t;
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
                          (thread_state_inv' t tsm)
                          (fun b -> thread_state_inv' t (update_if b tsm (M.vaddm tsm s s' p))))
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

noeq
type log_entry =
  | AddM : s:slot_id ->
           s':slot_id ->
           p:erased M.payload ->
           r:T.record { Some r == M.record_of_payload p } ->
           log_entry

  | AddB : s:slot_id ->
           ts:T.timestamp ->
           tid:T.thread_id ->
           p:erased M.payload ->
           r:T.record { Some r == M.record_of_payload p } ->
           log_entry

  | RunApp of runApp_payload
  | EvictM of evictM_payload
  | EvictB of evictB_payload
  | EvictBM of evictBM_payload
  | NextEpoch
  | VerifyEpoch



//TODO: parse one entry from the log and dispatch to
//      the appropriate function


// let verify_one (#tsm:M.thread_state_model)
//                (t:thread_state_t) //handle to the thread state
//                (#log_bytes:erased bytes)
//                (#loglen:U32.t)
//                (logpos:U32.t { U32.v logpos <= U32.v loglen })
//                (log:larray U8.t loglen) //concrete log
//                (#outlen:U32.t)
//                (outpos:U32.t { U32.v outpos <= U32.v outlen })
//                (out:larray U8.t outlen) //out array, to write outputs
//                (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
//   = admit__()

// // /// Entry point to run a single verifier thread on a log
// let verify (#tsm:M.thread_state_model)
//            (t:thread_state_t) //handle to the thread state
//            (#log_bytes:erased bytes)
//            (#len:U32.t)
//            (log:larray U8.t len) //concrete log
//            (#outlen:U32.t)
//            (out:larray U8.t outlen) //out array, to write outputs
//            (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
//   = admit__()
