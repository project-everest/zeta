module Zeta.Correctness

open Zeta.App
open Zeta.AppSimulate
open Zeta.Steel.ApplicationTypes
open Zeta.Steel.ThreadStateModel
open Zeta.Steel.MultiSetHash
open Zeta.Steel.Rel
open Zeta.Steel.ThreadRel
open Zeta.Steel.GlobalRel

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HA = Zeta.Steel.HashAccumulator
module GG = Zeta.Generic.Global

let hash_collision = Zeta.HashCollision.hash_collision app

(* Do we really need this for ghost reasoning? *)
let mset_equal (ms1 ms2: mset)
  : b: bool { b <==> ms1 == ms2 }
  = admit()

let rec search_epoch (epmax: i_epoch)
                     (logs: i_verifiable_logs)
  : GTot (o:option i_epoch
    {
      None? o /\ GG.aems_equal_upto epmax logs
      \/
      Some? o /\ ~ (GG.add_set (Some?.v o) logs == GG.evict_set (Some?.v o) logs) /\
      Some?.v o <= epmax
    })
    (decreases epmax)
  = if mset_equal (GG.add_set epmax logs) (GG.evict_set epmax logs) then
      if epmax = 0 then None
      else search_epoch (epmax - 1) logs
    else
      Some epmax

let aems_equal_or_hash_collision (epmax: epoch_id)
                                 (logs: all_logs {verifiable_and_certified logs epmax})
  : GTot (o:option ms_hash_collision
    {
      let i_logs = to_ilog logs in
      let i_epmax = lift_epoch epmax in
      None? o /\ GG.aems_equal_upto i_epmax i_logs
      \/
      Some? o
    })
  = let i_logs = to_ilog logs in
    let i_epmax = lift_epoch epmax in
    let o = search_epoch i_epmax i_logs in

    if None = o then
      None
    else (
      let i_ep = Some?.v o in
      let add_set = GG.add_set i_ep i_logs in
      let evict_set = GG.evict_set i_ep i_logs in
      assert(add_set =!= evict_set);

      assert(i_ep <= i_epmax);
      let ep = U32.uint_to_t i_ep in
      assert(epoch_is_certified logs ep);
      certified_epoch_aggregate_hashes_equal logs ep;
      aggr_add_hash_correct logs ep;
      aggr_evict_hash_correct logs ep;
      Some (MSCollision add_set evict_set)
    )

(* the definition of epoch_is_certified may need to be adjusted ... *)
let main_lemma (epmax: epoch_id)
               (logs: all_logs {verifiable_and_certified logs epmax /\
                                ~ (seq_consistent (all_app_fcrs epmax logs))})
  : GTot (either hash_collision ms_hash_collision)
  = let o = aems_equal_or_hash_collision epmax logs in
    let i_logs = to_ilog logs in
    let i_epmax = lift_epoch epmax in
    let i_fcrs = GG.app_fcrs_within_ep i_epmax i_logs in
    all_app_fcrs_rel epmax logs;
    assert(~ (seq_consistent i_fcrs));
    if Some? o then
      Inr (Some?.v o)
    else
      Inl (Zeta.Intermediate.Correctness.lemma_verifier_correct i_epmax i_logs)
