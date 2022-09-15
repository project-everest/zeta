module Zeta.Steel.Main
open FStar.Ghost
open Zeta.Steel.ApplicationTypes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Zeta.Steel.FormatsManual
open Steel.ST.Util
open Zeta.Steel.Util

module A = Steel.ST.Array
module G = Steel.ST.GhostReference
module Lock = Steel.ST.SpinLock
module TLM = Zeta.Steel.ThreadLogMap

module T = Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel
module AEH = Zeta.Steel.AggregateEpochHashes
module V = Zeta.Steel.Verifier
module SA = Zeta.SeqAux
#push-options "--ide_id_info_off"

[@@noextract_to "krml"]
noextract
let tid_log_map = 
  x:Map.t tid (option M.log) { 
    Map.domain x `Set.equal` Set.complement Set.empty 
  }

[@@CAbstractStruct]
val top_level_state (b: Ghost.erased bool) : Type0

val core_inv (#b: Ghost.erased bool) (t:top_level_state b) : vprop

val core_inv_share (#opened: _) (#b: _) (t: top_level_state b) : STGhostT unit opened
  (core_inv t) (fun _ -> core_inv t `star` core_inv t)

val core_inv_gather (#opened: _) (#b: _) (t: top_level_state b) : STGhostT unit opened
  (core_inv t `star` core_inv t) (fun _ -> core_inv t)

val all_logs (t:top_level_state true) (_ : tid_log_map) : vprop

val log_of_tid (t:top_level_state true) (tid:tid) (l:M.log) : vprop

// Extract a thread log
val all_logs_log_of_tid
  (#opened: _)
  (t: top_level_state true)
  (m: tid_log_map)
  (tid: tid)
  (prf: squash (Some? (Map.sel m tid)))
: STGhostT unit opened
  (all_logs t m)
  (fun _ -> all_logs t (Map.upd m tid None) `star` log_of_tid t tid (Some?.v (Map.sel m tid)))

(*
// Freeze all remaining thread logs (meant to be used after extracting logs for all threads)
val frozen_logs (t: top_level_state) (m: tid_log_map) : vprop

val freeze_all_logs
  (#opened: _)
  (t: top_level_state)
  (m: tid_log_map)
: STGhostT unit opened
    (all_logs t m)
    (fun _ -> frozen_logs t m)

val frozen_logs_share
  (#opened: _)
  (t: top_level_state)
  (m: tid_log_map)
: STGhostT unit opened
    (frozen_logs t m)
    (fun _ -> frozen_logs t m `star` frozen_logs t m)

val frozen_logs_gather
  (#opened: _)
  (t: top_level_state)
  (m: tid_log_map)
: STGhostT unit opened
    (frozen_logs t m `star` frozen_logs t m)
    (fun _ -> frozen_logs t m)
*)

val snapshot (#b: Ghost.erased bool) (t:top_level_state b) (_ : tid_log_map) : vprop

module R = Steel.ST.Reference

let init_post
  (#b: Ghost.erased bool)
  (ts: top_level_state b)
: Tot vprop
= if b then all_logs ts (Map.const (Some Seq.empty)) else emp

// This creates a Zeta instance
val init (b: Ghost.erased bool)
  : STT (R.ref (top_level_state b))
        emp
        (fun r -> 
          exists_ (fun ts -> 
            R.pts_to r full ts `star`
            core_inv ts `star`
            init_post ts
        ))

let verify_post_success_pure_inv
  (incremental: Ghost.erased bool)
  (tid:tid)
  (entries:erased AEH.log)
  (log_bytes:erased bytes)
  (out_bytes:erased bytes)
  (read wrote:U32.t)  
  (entries':Seq.seq log_entry)
  (out_bytes':Seq.seq U8.t)
  : prop
  = Log.parse_log_up_to log_bytes (U32.v read) == Some entries' /\
    (let tsm = M.verify_model (M.init_thread_state_model tid) entries in
     let tsm' = M.verify_model tsm entries' in
     Ghost.reveal incremental == true ==> Application.n_out_bytes tsm tsm' 0ul wrote out_bytes out_bytes')

let log_of_tid_gen
  (#b: Ghost.erased bool)
  (t:top_level_state b) (tid:tid) (l:M.log)
: Tot vprop
= if b then log_of_tid t tid l else emp

[@@ __reduce__]
let verify_post_success_out_bytes_pred
  (#b: Ghost.erased bool)
  (t:top_level_state b)
  (tid:tid)
  (entries:erased AEH.log)
  (log_bytes:erased bytes)
  (out_len: U32.t)
  (out_bytes:erased bytes)
  (output:larray U8.t out_len)
  (read wrote:U32.t)
  (entries':Seq.seq log_entry)
  : Seq.seq U8.t -> vprop
  = fun out_bytes' ->
    log_of_tid_gen t tid (entries `Seq.append` entries')
      `star`
    A.pts_to output full_perm out_bytes'
      `star`
    pure (verify_post_success_pure_inv
            b
            tid
            entries
            log_bytes
            out_bytes
            read
            wrote
            entries'
            out_bytes')

[@@ __reduce__]
let verify_post_success_pred
  (#b: Ghost.erased bool)
  (t:top_level_state b)
  (tid:tid)
  (entries:erased AEH.log)
  (log_bytes:erased bytes)
  (out_len: U32.t)
  (out_bytes:erased bytes)
  (output:larray U8.t out_len)
  (read wrote:U32.t)
  : Seq.seq log_entry -> vprop
  = fun entries' ->
    exists_ (verify_post_success_out_bytes_pred
               t
               tid
               entries
               log_bytes
               out_len
               out_bytes
               output
               read
               wrote
               entries')

[@@__reduce__]
let exists_log_of_tid
  (t: top_level_state true)
  (tid: tid)
: vprop
= exists_ (fun entries' -> log_of_tid t tid entries')

let exists_log_of_tid_gen
  (#b: Ghost.erased bool)
  (t:top_level_state b)
  (tid:tid)
: vprop
= if b then exists_log_of_tid t tid else emp

let verify_result (len: U32.t) = v:V.verify_result { V.verify_result_complete len v }

let verify_post
  (#b: Ghost.erased bool)
  (t:top_level_state b)
  (tid:tid)
  (entries:erased AEH.log)
  (log_perm:perm)
  (log_bytes:erased bytes)
  (len: U32.t)
  (input:larray U8.t len)
  (out_len: U32.t)
  (out_bytes:erased bytes)
  (output:larray U8.t out_len)
  : post_t (option (verify_result len))
  = fun res ->
    core_inv t `star`
    A.pts_to input log_perm log_bytes `star`
    (match res with
     | Some (V.Verify_success read wrote) ->
       exists_ (verify_post_success_pred
                  t
                  tid
                  entries
                  log_bytes
                  out_len
                  out_bytes
                  output
                  read
                  wrote)

     | _ ->
       exists_ (fun s -> A.pts_to output full_perm s) `star`
       exists_log_of_tid_gen t tid
    )

val verify_log (#p:perm)
               (#b: Ghost.erased bool)
               (#t:erased (top_level_state b))
               (r:R.ref (top_level_state b))
               (tid:tid)
               (#entries:erased AEH.log)
               (#log_perm:perm)
               (#log_bytes:erased bytes)
               (len: U32.t { len <> 0ul })
               (input:larray U8.t len)
               (out_len: U32.t)
               (#out_bytes:erased bytes)
               (output:larray U8.t out_len)
  : STT (option (verify_result len))
    (R.pts_to r p t `star`
     core_inv t `star`
     A.pts_to input log_perm log_bytes `star`
     A.pts_to output full_perm out_bytes `star`
     log_of_tid_gen t tid entries)
    (fun res -> 
       R.pts_to r p t `star`
       verify_post t tid entries log_perm log_bytes len input out_len out_bytes output res)

let read_max_post (#b: Ghost.erased bool) (t:top_level_state b) (res:AEH.max_certified_epoch_result)
  : vprop
  = match res with
    | AEH.Read_max_error  //underspec: overflow or element went missing in IArray
    | AEH.Read_max_none -> emp  //no epoch has been certified yet
    | AEH.Read_max_some max ->
      exists_ (fun logs ->
        snapshot t (AEH.map_of_seq logs)
        `star`
        pure (Zeta.Correctness.sequentially_consistent_app_entries_except_if_hash_collision logs max))
        
val max_certified_epoch (#p:perm)
                        (#b: Ghost.erased bool)
                        (#t:erased (top_level_state b))
                        (r:R.ref (top_level_state b))
  : STT AEH.max_certified_epoch_result
        (R.pts_to r p t)
        (fun res -> 
           R.pts_to r p t `star`
           read_max_post t res)
//From this, we should connect back to the semantic
//proof and show that the entries are sequentially consistent up to eid
//except for hash collisions

let read_store : VerifierTypes.read_store_t = Zeta.Steel.VerifierTypes.read_store
let write_store : VerifierTypes.write_store_t = Zeta.Steel.VerifierTypes.write_store
