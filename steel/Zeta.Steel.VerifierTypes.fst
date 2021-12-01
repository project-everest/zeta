module Zeta.Steel.VerifierTypes

open FStar.Ghost
open Steel.ST.Util
module A = Steel.ST.Array
module R = Steel.ST.Reference
module G = Steel.ST.GhostReference

open Zeta.Steel.ApplicationTypes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Zeta.Steel.ApplicationTypes
open Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel

open Zeta.Steel.FormatsManual
open Zeta.Steel.Util
module T = Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel
module AEH = Zeta.Steel.AggregateEpochHashes
module IArray = Zeta.Steel.IArray
module HA = Zeta.Steel.HashAccumulator
#push-options "--ide_id_info_off"

let vstore
  : Type0
  = a:A.array (option M.store_entry) {
       A.length a == U16.v store_size
    }

noeq
type thread_state_t = {
  thread_id    : T.thread_id;
  failed       : R.ref bool;
  store        : vstore;
  clock        : R.ref U64.t;
  epoch_hashes : AEH.all_epoch_hashes;
  processed_entries: G.ref (Seq.seq log_entry_base);
  app_results  : G.ref M.app_results;
  serialization_buffer: A.larray U8.t 4096
}

let thread_id t = t.thread_id

[@@__reduce__]
let thread_state_inv (t:thread_state_t)
                     ([@@@smt_fallback] tsm:M.thread_state_model)
  : vprop
  = R.pts_to t.failed full tsm.failed `star`
    A.pts_to t.store tsm.store `star`
    R.pts_to t.clock full tsm.clock `star`
    IArray.perm t.epoch_hashes tsm.epoch_hashes Set.empty `star`
    G.pts_to t.processed_entries full tsm.processed_entries `star`
    G.pts_to t.app_results full tsm.app_results `star`
    exists_ (A.pts_to t.serialization_buffer) `star`
    pure (tsm == M.verify_model
                   (M.init_thread_state_model t.thread_id)
                   tsm.processed_entries)

let elim_thread_state_inv (#o:_) (#tsm:M.thread_state_model) (t:thread_state_t)
  : STGhost unit o
    (thread_state_inv t tsm)
    (fun _ -> thread_state_inv t tsm)
    (requires True)
    (ensures fun _ ->
      tsm == M.verify_model (M.init_thread_state_model (thread_id t))
                            tsm.processed_entries)
  = extract_pure _
