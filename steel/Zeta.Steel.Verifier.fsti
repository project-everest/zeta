module Zeta.Steel.Verifier
include Zeta.Steel.VerifierTypes
open FStar.Ghost
open Zeta.Steel.ApplicationTypes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Zeta.Steel.FormatsManual
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
open Steel.Array

module T = Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel
module A = Steel.Array
module AEH = Zeta.Steel.AggregateEpochHashes

#push-options "--ide_id_info_off"

val spec_parser_log : Zeta.Steel.Parser.spec_parser (Seq.seq log_entry_base)

val create (tid:T.thread_id)
  : Steel thread_state_t
    emp
    (fun t -> thread_state_inv t)
    (requires fun h -> True)
    (ensures fun _ vs h1 ->
      value_of vs h1 == M.init_thread_state_model tid)

module P = Zeta.Steel.Parser

val serialized_new_app_results (init final:M.app_results)
                               (n_out:U32.t)
                               (out: P.bytes)
  : prop

let log_entries = Seq.seq log_entry_base

let committed_prefix (l0 l1:log_entries) : prop = True

[@@ __steel_reduce__]
let ghost_sel (#a:Type)
              (#p:vprop)
              (q:Steel.FractionalPermission.perm)
              (r:ghost_ref a)
              (h:rmem p{
                FStar.Tactics.with_tactic
                  selector_tactic
                  (can_be_split p (ghost_vptrp r q) /\ True)
              })
  = h (ghost_vptrp r q)

val verify (t:thread_state_t)
           (len:U32.t) (log:A.array U8.t)
           (outlen:U32.t) (out:A.array U8.t)
           (logrefs: erased (AEH.log_refs_t))
           (aeh:AEH.aggregate_epoch_hashes logrefs)
           (mylogref:AEH.log_ref)
  : Steel U32.t
    (thread_state_inv t `star`
     (A.varray log `star`
      A.varray out `star`
      ghost_vptrp mylogref AEH.half))
    (fun _ ->
      thread_state_inv t `star`
      (A.varray log `star`
       A.varray out `star`
       ghost_vptrp mylogref AEH.half))
    (requires fun h ->
      let tsm = value_of t (focus_rmem h _) in
      let committed_entries = ghost_sel AEH.half mylogref h in
      U32.v len == A.length log /\
      U32.v outlen = A.length out /\
      Map.sel logrefs tsm.thread_id == mylogref  /\
      committed_prefix committed_entries tsm.processed_entries
      )
    (ensures fun h0 n_out h1 ->
      let tsm0 = value_of t (focus_rmem h0 _) in
      let tsm1 = value_of t (focus_rmem h1 _) in
      let log_bytes = A.asel log h0 in
      let out_bytes = A.asel out h1 in
      let committed_entries = ghost_sel AEH.half mylogref h1 in
      log_bytes == A.asel log h1 /\ //log unchanged
      (match spec_parser_log log_bytes with
       | None -> tsm1.failed
       | Some (log_entries, n) ->
         if n = U32.v len
         then ( //parsing succeeded
           tsm1 == M.verify_model tsm0 log_entries /\
           serialized_new_app_results tsm0.app_results tsm1.app_results n_out out_bytes /\
           committed_prefix tsm1.processed_entries committed_entries
         )
         else tsm1.failed))
