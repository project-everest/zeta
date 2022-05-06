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
  = let aeh = AH.aggregate_all_threads_epoch_hashes ep (as_tid_logs logs) in
    aeh.hadd

let aggregate_evict_hash (logs: all_logs) (ep: epoch_id)
  : GTot hash_value_t
  = let aeh = AH.aggregate_all_threads_epoch_hashes ep (as_tid_logs logs) in
    aeh.hevict
  
let certified_epoch_aggregate_hashes_equal (logs: all_logs) (ep: epoch_id {AH.epoch_is_certified (as_tid_logs logs) ep})
  : Lemma (ensures (aggregate_add_hash logs ep = aggregate_evict_hash logs ep))
  = ()

let all_valid_tsms = tsms: Seq.seq thread_state_model
    { forall i. ThreadRel.valid (Seq.index tsms i) }

let all_epoch_completed (ep: epoch_id) (tsms: Seq.seq thread_state_model)
  = forall (i:Zeta.SeqAux.seq_index tsms). AH.is_epoch_verified (Seq.index tsms i) ep
  
let all_add_sets  (tsms: all_valid_tsms) (ep: epoch_id)
  : GTot (Seq.seq mset)
  = let i_ep = lift_epoch ep in
    Seq.init_ghost (Seq.length tsms) (fun i -> add_set (Seq.index tsms i) i_ep)

let all_evict_sets  (tsms: all_valid_tsms) (ep: epoch_id)
  : GTot (Seq.seq mset)
  = let i_ep = lift_epoch ep in
    Seq.init_ghost (Seq.length tsms) (fun i -> evict_set (Seq.index tsms i) i_ep)

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
  = let tid_logs = as_tid_logs logs in
    let tsms = Zeta.SeqAux.map (fun (tid, _) -> AH.tsm_of_log tid_logs tid) tid_logs in
    assert (forall (tid:tid). Seq.index tsms (U16.v tid) == AH.tsm_of_log tid_logs tid);
    introduce forall (tid:tid). let tsm = AH.tsm_of_log tid_logs tid in 
                           not (tsm.failed) /\
                           tsm.thread_id == tid /\
                           tsm == run tid tsm.processed_entries
    with (
      let tsm = AH.tsm_of_log tid_logs tid in
      TSM.verify_model_thread_id_inv (init_thread_state_model tid) 
                                     (AH.log_of_tid tid_logs tid);
      TSM.tsm_entries_invariant_steps tid (AH.log_of_tid tid_logs tid)                                     
    );
    tsms


#push-options "--fuel 1 --ifuel 1 --query_stats"
let valid_spec_rel_tsm (t:tid) (l:log)
  : Lemma 
    (let tsm = TSM.verify_model (TSM.init_thread_state_model t) l in
     tsm.failed \/ (
     ThreadRel.valid tsm /\
     ThreadRel.spec_rel tsm))
  = let tsm = TSM.verify_model (TSM.init_thread_state_model t) l in
    TSM.tsm_entries_invariant_steps t l;
    if tsm.failed
    then ()
    else (
      ThreadRel.valid_implies_spec_rel tsm
    )


let thread_contrib_of_log_for_epoch (t:tid) (l:log) (e:epoch_id)
  : Lemma 
    (requires (
      let tsm = TSM.verify_model (TSM.init_thread_state_model t) l in
      AH.is_epoch_verified tsm e))
    (ensures (
      let tsm = TSM.verify_model (TSM.init_thread_state_model t) l in    
      valid_spec_rel_tsm t l;
      Map.sel (AH.thread_contrib_of_log t l) e ==  Map.sel tsm.epoch_hashes e /\
      (Map.sel tsm.epoch_hashes e == ({ hadd = ms_hashfn (ThreadRel.add_set tsm (lift_epoch e));
                                        hevict = ms_hashfn (ThreadRel.evict_set tsm (lift_epoch e))}))))
  = let tsm = TSM.verify_model (TSM.init_thread_state_model t) l in
    valid_spec_rel_tsm t l;
    ThreadRel.valid_hadd_prop e tsm;
    ThreadRel.valid_hevict_prop e tsm

let all_threads_hadd (logs:verifiable_logs) (ep:epoch_id)
  : GTot (Seq.seq TSM.model_hash)
  = Zeta.SeqAux.map ms_hashfn (all_add_sets (to_tsms logs) ep)

let all_threads_hevict (logs:verifiable_logs) (ep:epoch_id)
  : GTot (Seq.seq TSM.model_hash)
  = Zeta.SeqAux.map ms_hashfn (all_evict_sets (to_tsms logs) ep)

module CE = FStar.Algebra.CommMonoid.Equiv

let aggregate_model_hash_equiv 
  : CE.equiv TSM.model_hash
  = CE.EQ ( == ) (fun _ -> ()) (fun _ _ -> ()) (fun _ _ _ -> ())

let aggregate_model_hash_monoid
  : CE.cm TSM.model_hash aggregate_model_hash_equiv
  = CE.CM HA.initial_hash
          HA.aggregate_hashes
          HA.initial_hash_unit 
          HA.aggregate_hashes_associative
          HA.aggregate_hashes_commutative
          (fun _ _ _ _ -> ())
  
let aggregate_hashes (s:Seq.seq TSM.model_hash)
  : TSM.model_hash
  = FStar.Seq.Permutation.foldm_snoc aggregate_model_hash_monoid s
        
let aggregate_all_threads_hadd (logs:verifiable_logs) (ep:epoch_id)
  : GTot TSM.model_hash
  = aggregate_hashes (all_threads_hadd logs ep)

let aggregate_all_threads_hevict (logs:verifiable_logs) (ep:epoch_id)
  : GTot TSM.model_hash
  = aggregate_hashes (all_threads_hevict logs ep)

let split_aggregate_all_threads_epoch_hashes (logs:verifiable_logs)
                                             (ep:TSM.epoch_id)
  : Lemma 
    (AH.aggregate_all_threads_epoch_hashes ep (as_tid_logs logs) ==
      ({ hadd = aggregate_all_threads_hadd logs ep;
         hevict = aggregate_all_threads_hevict logs ep }))
  = admit()

let map_seq_mset #a (f:Zeta.MultiSet.cmp a) (s:Zeta.SSeq.sseq a) (i:nat{i < Seq.length s}) = Zeta.MultiSet.seq2mset #_ #f (Seq.index s i)

let union_all_sseq (#a: eqtype) (f: Zeta.MultiSet.cmp a) (s: Zeta.SSeq.sseq a)
  : Lemma (ensures (sseq2mset #_ #f s == union_all (Seq.init (Seq.length s) (map_seq_mset f s))))
  = assert (sseq2mset #_ #f s == union_all (Seq.init (Seq.length s) (map_seq_mset f s)))
         by FStar.Tactics.(norm [delta_only [`%map_seq_mset]];
                           mapply (`union_all_sseq))

#push-options "--print_implicits --print_bound_var_types"
module ZIV = Zeta.Intermediate.Verifier

let hash_union_commute (msets:Seq.seq mset)
  : Lemma (aggregate_hashes (Zeta.SeqAux.map ms_hashfn msets) ==
           ms_hashfn (union_all msets))
  = admit()
  
let aggr_add_hash_correct_alt (logs: verifiable_logs) (ep: epoch_id)
  : Lemma (requires (AH.epoch_is_certified (as_tid_logs logs) ep))
          (ensures (let gl = to_ilog logs in
                    let i_ep = lift_epoch ep in
                    let hadd = ms_hashfn (GG.add_set i_ep gl) in
                    aggregate_all_threads_hadd logs ep  == hadd))
  = let rhs = aggregate_all_threads_hadd logs ep in
    let gl = to_ilog logs in
    let i_ep = lift_epoch ep in
    let lhs = ms_hashfn (GG.add_set i_ep gl) in
    let ss = (GG.add_sseq i_ep gl) in
    let vspec = (ZIV.int_verifier_spec_base i_vcfg)  in
    calc (==) {
      GG.add_set #vspec i_ep gl;
    (==) {}
      sseq2mset #_ #(Zeta.MultiSetHashDomain.ms_hashfn_dom_cmp (ZIV.int_verifier_spec_base i_vcfg).app) (GG.add_sseq (lift_epoch ep) (to_ilog logs));
    (==)  { union_all_sseq (Zeta.MultiSetHashDomain.ms_hashfn_dom_cmp vspec.app) (GG.add_sseq (lift_epoch ep) (to_ilog logs)) }
      union_all (Seq.init (Seq.length gl) 
                          (map_seq_mset _ (GG.add_sseq (lift_epoch ep) (to_ilog logs))));
    (==) { 
            assert (forall (i:Zeta.SeqAux.seq_index ss). Seq.index ss i == Zeta.Generic.Thread.add_seq i_ep (GG.index gl i));
            assert (forall (i:Zeta.SeqAux.seq_index ss). Zeta.MultiSet.seq2mset (Seq.index ss i) == ThreadRel.add_set (Seq.index (to_tsms logs) i) i_ep);
            assert ((Seq.init (Seq.length gl) (map_seq_mset _ ss) `Seq.equal`
                     all_add_sets (to_tsms logs) ep))
         }
      union_all (all_add_sets (to_tsms logs) ep);
    };
    hash_union_commute (all_add_sets (to_tsms logs) ep)

let aggr_add_hash_correct (logs: verifiable_logs) (ep: epoch_id)
  : Lemma (requires (AH.epoch_is_certified (as_tid_logs logs) ep))
          (ensures (let gl = to_ilog logs in
                    let i_ep = lift_epoch ep in
                    let add_set = GG.add_set i_ep gl in
                    let h = aggregate_add_hash logs ep in
                    h = ms_hashfn add_set))
  = split_aggregate_all_threads_epoch_hashes logs ep;
    aggr_add_hash_correct_alt logs ep

#pop-options

#push-options "--z3rlimit_factor 2"
let aggr_evict_hash_correct_alt (logs: verifiable_logs) (ep: epoch_id)
  : Lemma (requires (AH.epoch_is_certified (as_tid_logs logs) ep))
          (ensures (let gl = to_ilog logs in
                    let i_ep = lift_epoch ep in
                    let hev = ms_hashfn (GG.evict_set i_ep gl) in
                    aggregate_all_threads_hevict logs ep  == hev))
  = let gl = to_ilog logs in
    let i_ep = lift_epoch ep in
    let lhs = ms_hashfn (GG.evict_set i_ep gl) in
    let ss = (GG.evict_sseq i_ep gl) in
    let vspec = (ZIV.int_verifier_spec_base i_vcfg)  in
    calc (==) {
      GG.evict_set #vspec i_ep gl;
    (==) {}
      sseq2mset #_ #(Zeta.MultiSetHashDomain.ms_hashfn_dom_cmp (ZIV.int_verifier_spec_base i_vcfg).app) (GG.evict_sseq (lift_epoch ep) (to_ilog logs));
    (==)  { union_all_sseq (Zeta.MultiSetHashDomain.ms_hashfn_dom_cmp vspec.app) (GG.evict_sseq (lift_epoch ep) (to_ilog logs)) }
      union_all (Seq.init (Seq.length gl) 
                          (map_seq_mset _ (GG.evict_sseq (lift_epoch ep) (to_ilog logs))));
    (==) { 
            assert (forall (i:Zeta.SeqAux.seq_index ss). Seq.index ss i == Zeta.Generic.Thread.evict_seq i_ep (GG.index gl i));
            assert (forall (i:Zeta.SeqAux.seq_index ss). Zeta.MultiSet.seq2mset (Seq.index ss i) == ThreadRel.evict_set (Seq.index (to_tsms logs) i) i_ep);
            assert ((Seq.init (Seq.length gl) (map_seq_mset _ ss) `Seq.equal`
                     all_evict_sets (to_tsms logs) ep))
         }
      union_all (all_evict_sets (to_tsms logs) ep);
    };
    hash_union_commute (all_evict_sets (to_tsms logs) ep)
#pop-options

let aggr_evict_hash_correct (logs: verifiable_logs) (ep: epoch_id)
  : Lemma (requires (AH.epoch_is_certified (as_tid_logs logs) ep))
          (ensures (let gl = to_ilog logs in
                    let i_ep = lift_epoch ep in
                    let evict_set = GG.evict_set i_ep gl in
                    let h = aggregate_evict_hash logs ep in
                    h = ms_hashfn evict_set))
  = split_aggregate_all_threads_epoch_hashes logs ep;
    aggr_evict_hash_correct_alt logs ep

