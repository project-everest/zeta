module Zeta.Steel.SafeMain

module M = Zeta.Steel.Main
module AEH = Zeta.Steel.AggregateEpochHashes
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module U = Zeta.Steel.Util
module V = Zeta.Steel.Verifier
module A = Steel.ST.Array
module AT = Zeta.Steel.ApplicationTypes
module EXT = Zeta.Steel.ExternalPtr
module U16 = FStar.UInt16
module TSM = Zeta.Steel.ThreadStateModel

open Steel.ST.Util

val handle_pts_to
  (ts: M.top_level_state false)
: Tot vprop

val gather
  (#opened: _)
  (ts1: M.top_level_state false)
  (ts2: M.top_level_state false)
: STGhost unit opened
    (handle_pts_to ts1 `star` handle_pts_to ts2)
    (fun _ -> handle_pts_to ts1)
    True
    (fun _ -> ts1 == ts2)

val share
  (#opened: _)
  (ts: M.top_level_state false)
: STGhostT unit opened
    (handle_pts_to ts)
    (fun _ -> handle_pts_to ts `star` handle_pts_to ts)

[@__reduce__]
let verify_pre
    (len: U32.t)
    (input: EXT.extern_input_ptr)
    (out_bytes: AT.bytes)
    (output: EXT.extern_output_ptr)
: Tot vprop
=
     EXT.has_extern_input_ptr input len `EXT.sl_and` // NOT a separating conjunct, need to explicitly check for disjointness
     A.pts_to (EXT.gtake output) full_perm out_bytes

inline_for_extraction
let check_verify_input
  (tid: U16.t)
  (len: U32.t)
  (input: EXT.extern_input_ptr)
  (out_len: U32.t)
  (output: EXT.extern_output_ptr)
: Tot bool
= FStar.Int.Cast.uint16_to_uint32 tid `U32.lt` AT.n_threads &&
  len <> 0ul &&
  EXT.valid_input input len &&
  EXT.valid_output output out_len

let verify_post_success_pure_inv
  (tid:AT.tid)
  (out_bytes:Ghost.erased AT.bytes)
  (read wrote:U32.t)  
  (out_bytes':Seq.seq U8.t)
  : prop
  =
    (exists (log_bytes: AT.bytes) (entries entries': AEH.log) . (
      let tsm = TSM.verify_model (TSM.init_thread_state_model tid) entries in
     let tsm' = TSM.verify_model tsm entries' in
     Log.parse_log_up_to log_bytes (U32.v read) == Some entries' /\
     Application.n_out_bytes tsm tsm' 0ul wrote out_bytes out_bytes'
    ))

[@@__reduce__]
let verify_post_some_m_success
  (tid:U16.t)
  (len: U32.t)
  (input: EXT.extern_input_ptr)
  (out_len: U32.t)
  (out_bytes: AT.bytes)
  (output: EXT.extern_output_ptr)
  (v: option (M.verify_result len))
  (sq: squash (check_verify_input tid len input out_len output))
  (t: M.top_level_state false)
  (read:U32.t)
  (wrote:U32.t)
: Tot vprop
=
      EXT.has_extern_input_ptr input len `star`
       exists_ (fun out_bytes' ->
       A.pts_to (EXT.gtake output) full_perm out_bytes'
           `star`
         pure (verify_post_success_pure_inv
            tid
            out_bytes
            read
            wrote
            out_bytes')
       )

[@@__reduce__]
let verify_post_some_m_failure
  (len: U32.t)
  (input: EXT.extern_input_ptr)
  (output: EXT.extern_output_ptr)
: Tot vprop
= exists_ (fun s -> 
    EXT.has_extern_input_ptr input len `EXT.sl_and` // NOT a separating conjunct!
    A.pts_to (EXT.gtake output) full_perm s
  )

let verify_post_some_m
  (tid:U16.t)
  (len: U32.t)
  (input: EXT.extern_input_ptr)
  (out_len: U32.t)
  (out_bytes: AT.bytes)
  (output: EXT.extern_output_ptr)
  (v: option (v:V.verify_result { V.verify_result_complete len v }))
  (t: M.top_level_state false)
: Tot vprop
= match v with
  | Some (V.Verify_success read wrote) ->
    if check_verify_input tid len input out_len output
    then
      verify_post_some_m_success tid len input out_len out_bytes output v () t read wrote
    else
      pure False
  | _ -> verify_post_some_m_failure len input output 

[@@__reduce__]
let verify_post_some
  (tid:U16.t)
  (len: U32.t)
  (input: EXT.extern_input_ptr)
  (out_len: U32.t)
  (out_bytes: AT.bytes)
  (output: EXT.extern_output_ptr)
  (v: option (v:V.verify_result { V.verify_result_complete len v }))
: Tot vprop
= 
    exists_ (fun t ->
      handle_pts_to t `star`
      verify_post_some_m tid len input out_len out_bytes output v t
    )

let verify_post
  (tid:U16.t)
  (len: U32.t)
  (input: EXT.extern_input_ptr)
  (out_len: U32.t)
  (out_bytes: AT.bytes)
  (output: EXT.extern_output_ptr)
  (res: option (M.verify_result len))
: Tot vprop
= verify_post_some tid len input out_len out_bytes output res

val verify_log
               (tid:U16.t)
               (len: U32.t)
               (input: EXT.extern_input_ptr)
               (out_len: U32.t)
               (#out_bytes:Ghost.erased AT.bytes)
               (output: EXT.extern_output_ptr)
  : STT (option (M.verify_result len))
    (verify_pre len input out_bytes output)
    (fun res -> verify_post tid len input out_len out_bytes output res)

val max_certified_epoch
                        (_: unit)
  : STT AEH.max_certified_epoch_result
        emp
        (fun res -> exists_ (fun t ->
          handle_pts_to t `star`
          M.read_max_post t res
        ))
