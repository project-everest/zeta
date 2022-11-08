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
module EpochMap = Zeta.Steel.EpochMap
module HA = Zeta.Steel.HashAccumulator
open Zeta.Steel.EpochHashes
#push-options "--ide_id_info_off"

let vstore
  : Type0
  = a:A.array (option M.store_entry) {
       A.length a == U16.v store_size
    }

noeq
type thread_state_t = {
  thread_id    : tid;
  failed       : R.ref bool;
  store        : vstore;
  clock        : R.ref T.timestamp;
  last_evict_key : R.ref T.base_key;
  epoch_hashes : AEH.all_epoch_hashes;
  last_verified_epoch: R.ref (option M.epoch_id);
  processed_entries: G.ref (Seq.seq log_entry);
  app_results  : G.ref M.app_results;
  serialization_buffer: A.larray U8.t 4096;
  hasher       : HashValue.hasher_t
}

let thread_id t = t.thread_id

[@@__reduce__]
let thread_state_inv_core (t:thread_state_t)
                      ([@@@smt_fallback] tsm:M.thread_state_model)
  : vprop
  = R.pts_to t.failed full tsm.failed `star`
    array_pts_to t.store tsm.store `star`
    R.pts_to t.clock full tsm.clock `star`
    R.pts_to t.last_evict_key full tsm.last_evict_key `star`
    EpochMap.full_perm t.epoch_hashes M.init_epoch_hash tsm.epoch_hashes `star`
    R.pts_to t.last_verified_epoch full tsm.last_verified_epoch `star`
    G.pts_to t.processed_entries full tsm.processed_entries `star`
    G.pts_to t.app_results full tsm.app_results `star`
    exists_ (array_pts_to t.serialization_buffer) `star`
    HashValue.inv t.hasher

let intro_thread_state_inv_core #o
                           (tsm:M.thread_state_model)
                           (#f:_)
                           (#s:_)
                           (#c:_)
                           (#lev:_)
                           (#eh:_)
                           (#lve:_)
                           (#pe:_)
                           (#ar:_)
                           (t:thread_state_t)
   : STGhost unit o
     (R.pts_to t.failed full f `star`
      array_pts_to t.store s `star`
      R.pts_to t.clock full c `star`
      R.pts_to t.last_evict_key full lev `star`      
      EpochMap.full_perm t.epoch_hashes M.init_epoch_hash eh `star`
      R.pts_to t.last_verified_epoch full lve `star`
      G.pts_to t.processed_entries full pe `star`
      G.pts_to t.app_results full ar `star`
      exists_ (array_pts_to t.serialization_buffer) `star`
      HashValue.inv t.hasher)
     (fun _ -> thread_state_inv_core t tsm)
     (requires
       tsm.failed == f /\
       tsm.store == s /\
       tsm.clock == c /\
       tsm.last_evict_key == lev /\
       tsm.epoch_hashes == eh /\
       tsm.last_verified_epoch == lve /\
       tsm.processed_entries == pe /\
       tsm.app_results == ar)
     (ensures fun _ ->
       True)
   = rewrite (R.pts_to t.failed _ _ `star`
              array_pts_to t.store _ `star`
              R.pts_to t.clock _ _ `star`
              R.pts_to t.last_evict_key _ _ `star`              
              EpochMap.full_perm t.epoch_hashes _ _ `star`
              R.pts_to t.last_verified_epoch _ _ `star`
              G.pts_to t.processed_entries _ _ `star`
              G.pts_to t.app_results _ _ `star`
              exists_ (array_pts_to t.serialization_buffer) `star`
              HashValue.inv t.hasher)
             (thread_state_inv_core t tsm)

[@@__reduce__]
let thread_state_inv (t:thread_state_t)
                     ([@@@smt_fallback] tsm:M.thread_state_model)
  : vprop
  = thread_state_inv_core t tsm `star`
    pure (tsm_entries_invariant tsm /\
          t.thread_id == tsm.thread_id)

let intro_thread_state_inv (#o:_) (#tsm:M.thread_state_model) (t:thread_state_t)
  = intro_pure (tsm_entries_invariant tsm /\
                t.thread_id == tsm.thread_id)

let elim_thread_state_inv (#o:_) (#tsm:M.thread_state_model) (t:thread_state_t)
  : STGhost unit o
    (thread_state_inv t tsm)
    (fun _ -> thread_state_inv_core t tsm)
    (requires True)
    (ensures fun _ ->
      thread_id t == tsm.thread_id /\
      tsm_entries_invariant tsm)
  = elim_pure _
module Cast = FStar.Int.Cast


let read_store #tsm t slot =
  let se_opt = A.read t.store (u16_as_size_t slot) in
  match se_opt with
  | None -> return None
  | Some (se : M.store_entry) ->
    return (Some ({ key = se.key;
                    value = se.value }))

let write_store #tsm t slot v =
  let se_opt = A.read t.store (u16_as_size_t slot) in
  match se_opt with
  | Some (se : M.store_entry) ->
    let se' = { se with value = v } in
    A.write t.store (u16_as_size_t slot) (Some se');
    return ()

let restore_thread_state_inv_app #_ #tsm t app_results processed_entries =
  G.write t.app_results app_results;
  G.write t.processed_entries processed_entries;
  intro_thread_state_inv t
  


