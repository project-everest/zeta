module Zeta.Steel.GlobalRel

open FStar.Classical
open Zeta.MultiSet.SSeq
module GT = Zeta.Generic.Thread
module TSM = Zeta.Steel.ThreadStateModel
module HA = Zeta.Steel.HashAccumulator
module MS = Zeta.MultiSet
module ThreadRel = Zeta.Steel.ThreadRel

let to_ilog_idx (logs: verifiable_logs) (i: nat{i < n_threads_v})
  : GTot (l:i_log {GT.verifiable (i,l)})
  = let t = U16.uint_to_t i in
    let tl = index logs t in
    let tsm = to_tsm tl in
    let (_,l) = to_ilog tsm in
    l

let to_ilog (logs: verifiable_logs)
  : GTot (i_logs: i_verifiable_logs {Seq.length i_logs = n_threads_v})
  = Seq.init_ghost n_threads_v (fun i -> to_ilog_idx logs i)

let all_app_fcrs_rel (ep: epoch_id) (logs: verifiable_logs)
  : Lemma (ensures (let s_fcrs = all_app_fcrs ep logs in
                    let i_logs = to_ilog logs in
                    let i_ep = lift_epoch ep in
                    let i_fcrs = GG.app_fcrs_within_ep i_ep i_logs in
                    s_fcrs = i_fcrs))
  = let s_fcrs = all_app_fcrs ep logs in
    let i_logs = to_ilog logs in
    let i_ep = lift_epoch ep in
    let i_fcrs = GG.app_fcrs_within_ep i_ep i_logs in

    let aux (i:_)
      : Lemma (ensures (Seq.index s_fcrs i == Seq.index i_fcrs i))
      = let t = U16.uint_to_t i in
        let tl = index logs t in
        assert(app_fcrs ep tl == Seq.index s_fcrs i);
        spec_rel_implies_same_fcrs ep tl;
        ()
    in
    forall_intro aux;
    assert(Seq.equal s_fcrs i_fcrs);
    ()

let aggregate_add_hash (logs: all_logs) (ep: epoch_id)
  : GTot hash_value_t
  = let tsms = TSM.run_all _ logs in
    //let aeh = AH.aggregate_all_threads_epoch_hashes epoch_id all_logs in
    //TSMS.aggregate_epoch_hashes tsms ep in
    //aeh.hadd
    admit()

let aggregate_evict_hash (logs: all_logs) (ep: epoch_id)
  : GTot hash_value_t
  = let tsms = TSM.run_all _ logs in
    //let aeh = TSM.aggregate_epoch_hashes tsms ep in
    //aeh.hevict
    admit()

let certified_epoch_aggregate_hashes_equal (logs: all_logs) (ep: epoch_id {AH.epoch_is_certified logs ep})
  : Lemma (ensures (aggregate_add_hash logs ep = aggregate_evict_hash logs ep))
  = ()

let all_valid_tsms = tsms: Seq.seq thread_state_model
    {forall i. ThreadRel.valid (Seq.index tsms i)}

let all_epoch_completed (ep: epoch_id) (tsms: Seq.seq thread_state_model)
  = (* (forall i. let tsm = Seq.index tsms i in
          let hash = Map.sel tsm.epoch_hashes ep in
          hash.epoch_complete) *)
    admit()

let all_add_sets  (tsms: all_valid_tsms) (ep: epoch_id)
  : GTot (Seq.seq mset)
  = let i_ep = lift_epoch ep in
    Seq.init_ghost (Seq.length tsms) (fun i -> add_set (Seq.index tsms i) i_ep)

let all_add_sets_cons (tsms: all_valid_tsms {Seq.length tsms > 0}) (ep: epoch_id)
  : Lemma (ensures (let add_sets = all_add_sets tsms ep in
                    let i_ep = lift_epoch ep in
                    Seq.tail add_sets == all_add_sets (Seq.tail tsms) ep /\
                    Seq.head add_sets == add_set (Seq.head tsms) i_ep))
  = let add_sets = all_add_sets tsms ep in
    let i_ep = lift_epoch ep in
    assert (Seq.head add_sets == add_set (Seq.head tsms) i_ep);
    let tail = Seq.tail tsms in

    let tail_add_sets = Seq.tail add_sets in
    let add_sets_tail = all_add_sets tail ep in

    let aux (i:_)
      : Lemma (ensures (Seq.index add_sets_tail i == Seq.index tail_add_sets i))
      = ()
    in
    forall_intro aux;
    assert(Seq.equal add_sets_tail tail_add_sets);
    ()

let union_all_add_set (tsms: all_valid_tsms) (ep: epoch_id)
  : GTot mset
  =  union_all (all_add_sets tsms ep)

let lemma_all_add_set_cons (tsms: all_valid_tsms {Seq.length tsms > 0}) (ep: epoch_id)
  : Lemma (ensures (let tail = Seq.tail tsms in
                    let hd = Seq.head tsms in
                    let i_ep = lift_epoch ep in
                    union_all_add_set tsms ep ==
                    MS.union (add_set hd i_ep)
                             (union_all_add_set tail ep)))
  = all_add_sets_cons tsms ep;
    union_all_cons (all_add_sets tsms ep)

let union_all_evict_set (tsms: all_valid_tsms) (ep: epoch_id)
  : GTot mset
  = let i_ep= lift_epoch ep in
    let sms = Seq.init_ghost (Seq.length tsms) (fun i -> evict_set (Seq.index tsms i) i_ep) in
    union_all sms

(*
let rec aggregate_epoch_hashes_prop (eid: epoch_id) (tsms: all_valid_tsms {all_epoch_completed eid tsms})
  : Lemma (ensures (let aeh = TSM.aggregate_epoch_hashes tsms eid in
                    aeh.hadd = ms_hashfn (union_all_add_set tsms eid)))
          (decreases (Seq.length tsms))
  = let add_set_union = union_all_add_set tsms eid in
    let i_ep = lift_epoch eid in
    let aeh = TSM.aggregate_epoch_hashes tsms eid in

    if Seq.length tsms = 0 then (
      union_all_empty (all_add_sets tsms eid);
      lemma_hashfn_empty()
    )
    else (
      let tsms' = Seq.tail tsms in
      assert (forall i. ThreadRel.valid (Seq.index tsms' i));
      assert(all_epoch_completed eid tsms');
      aggregate_epoch_hashes_prop eid tsms';
      let hd = Seq.head tsms in
      assert(not hd.failed);
      let tl_hash = aggregate_epoch_hashes tsms' eid in
      assert(tl_hash.hadd = ms_hashfn (union_all_add_set tsms' eid));
      let hd_hash = Map.sel hd.epoch_hashes eid in
      assert(hd_hash.epoch_complete);
      assert(aeh.hadd = HA.aggregate_hashes hd_hash.hadd tl_hash.hadd);
      valid_hadd_prop eid hd;
      assert(hd_hash.hadd = ms_hashfn (add_set hd i_ep));
      lemma_all_add_set_cons tsms eid;
      lemma_union (add_set hd i_ep) (union_all_add_set tsms' eid);
      ()
    )
*)

let to_tsms (logs: verifiable_logs)
  : all_valid_tsms
  = //let tsms = Seq.init (Seq.length logs) (fun i -> to_tsm (index logs i)) in
    admit()


#push-options "--fuel 1 --ifuel 1 --query_stats"

let aggr_add_hash_correct (logs: verifiable_logs) (ep: epoch_id)
  : Lemma (requires (AH.epoch_is_certified logs ep))
          (ensures (let gl = to_ilog logs in
                    let i_ep = lift_epoch ep in
                    let add_set = GG.add_set i_ep gl in
                    let h = aggregate_add_hash logs ep in
                    h = ms_hashfn add_set))
  = let h = aggregate_add_hash logs ep in
    let tsms = run_all _ logs in
    //assert (forall i. ThreadRel.valid (Seq.index tsms i));



  admit()

#pop-options

let aggr_evict_hash_correct (logs: verifiable_logs) (ep: epoch_id)
  : Lemma (requires (AH.epoch_is_certified logs ep))
          (ensures (let gl = to_ilog logs in
                    let i_ep = lift_epoch ep in
                    let evict_set = GG.evict_set i_ep gl in
                    let h = aggregate_evict_hash logs ep in
                    h = ms_hashfn evict_set))
  = admit()
