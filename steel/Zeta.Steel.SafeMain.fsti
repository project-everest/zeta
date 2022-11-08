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

inline_for_extraction
let check_verify_input
  (tid: U16.t)
  (len: U32.t)
: Tot bool
= FStar.Int.Cast.uint16_to_uint32 tid `U32.lt` AT.n_threads &&
  len <> 0ul

noextract
let verify_post_success_pure_inv
  (log_bytes out_bytes': AT.bytes)
  (tid:AT.tid)
  (read wrote:U32.t)  
  : prop
  =
    (exists (entries entries': AEH.log) (out_bytes: AT.bytes) . (
      let tsm = TSM.verify_model (TSM.init_thread_state_model tid) entries in
     let tsm' = TSM.verify_model tsm entries' in
     Log.parse_log_up_to log_bytes (U32.v read) == Some entries' /\
     Application.n_out_bytes tsm tsm' 0ul wrote out_bytes out_bytes'
    ))

[@@__reduce__]
let verify_post_some_m_success
  (tid:U16.t)
  (len:U32.t)
  (input output: EXT.extern_ptr)
  (sq: squash (check_verify_input tid len))
  (t: M.top_level_state false)
  (read wrote:U32.t)
: Tot vprop
=
  exists_ (fun log_bytes -> exists_ (fun out_bytes' ->
      EXT.extern_in_out_pts_to input output log_bytes (EXT.Written out_bytes') `star`
         pure (verify_post_success_pure_inv
            log_bytes out_bytes'
            tid
            read
            wrote)
  ))

[@@__reduce__]
let verify_post_some_m_failure_true
  (input output: EXT.extern_ptr)
: Tot vprop
= exists_ (fun log_bytes -> exists_ (EXT.extern_in_out_pts_to input output log_bytes))

let verify_post_some_m_failure_cases
  (input output: EXT.extern_ptr)
  (cases: bool)
: Tot vprop
= if cases then verify_post_some_m_failure_true input output else emp

[@@__reduce__]
let verify_post_some_m_failure
  (input output: EXT.extern_ptr)
: Tot vprop
=
  exists_ (verify_post_some_m_failure_cases input output)

let verify_post_some_m
  (tid:U16.t)
  (len:U32.t)
  (input output: EXT.extern_ptr)
  (v: option (M.verify_result len))
  (t: M.top_level_state false)
: Tot vprop
= match v with
  | Some (V.Verify_success read wrote) ->
    if check_verify_input tid len
    then
      verify_post_some_m_success tid len input output () t read wrote
    else
      pure False
  | _ -> verify_post_some_m_failure input output

[@@__reduce__]
let verify_post_some
  (tid:U16.t)
  (len:U32.t)
  (input output: EXT.extern_ptr)
  (v: option (M.verify_result len))
: Tot vprop
= 
    exists_ (fun t ->
      handle_pts_to t `star`
      verify_post_some_m tid len input output v t
    )

let verify_post
  (tid:U16.t)
  (len:U32.t)
  (input output: EXT.extern_ptr)
  (res: option (M.verify_result len))
: Tot vprop
= verify_post_some tid len input output res

val verify_log (tid:U16.t)
               (len out_len:U32.t)
               (input output: EXT.extern_ptr)
  : STT (option (M.verify_result len))
    emp
    (fun res -> verify_post tid len input output res)

val max_certified_epoch
                        (_: unit)
  : STT AEH.max_certified_epoch_result
        emp
        (fun res -> exists_ (fun t ->
          handle_pts_to t `star`
          M.read_max_post t res
        ))
