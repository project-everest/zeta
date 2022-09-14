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

open Steel.ST.Util

val handle_pts_to
  (ts: M.top_level_state)
: Tot vprop

val gather
  (#opened: _)
  (ts1: M.top_level_state)
  (ts2: M.top_level_state)
: STGhost unit opened
    (handle_pts_to ts1 `star` handle_pts_to ts2)
    (fun _ -> handle_pts_to ts1)
    True
    (fun _ -> ts1 == ts2)

val share
  (#opened: _)
  (ts: M.top_level_state)
: STGhostT unit opened
    (handle_pts_to ts)
    (fun _ -> handle_pts_to ts `star` handle_pts_to ts)

[@__reduce__]
let verify_pre
    (log_perm:perm)
    (log_bytes: AT.bytes)
    (input: EXT.extern_ptr)
    (out_bytes: AT.bytes)
    (output: EXT.extern_ptr)
: Tot vprop
=
     A.pts_to (EXT.gtake input) log_perm log_bytes `star`
     A.pts_to (EXT.gtake output) full_perm out_bytes

inline_for_extraction
let check_verify_input
  (tid: U16.t)
  (len: U32.t)
  (input: EXT.extern_ptr)
  (out_len: U32.t)
  (output: EXT.extern_ptr)
: Tot bool
= FStar.Int.Cast.uint16_to_uint32 tid `U32.lt` AT.n_threads &&
  len <> 0ul &&
  EXT.valid input len &&
  EXT.valid output out_len

[@@__reduce__]
let verify_post_some_m_success_body
  (tid:U16.t)
  (log_perm:perm)
  (log_bytes: AT.bytes)
  (len: U32.t)
  (input: EXT.extern_ptr)
  (out_len: U32.t)
  (out_bytes: AT.bytes)
  (output: EXT.extern_ptr)
  (v: option (v:V.verify_result { V.verify_result_complete len v }))
  (sq: squash (check_verify_input tid len input out_len output))
  (t: M.top_level_state)
  (entries: _)
  (read:U32.t)
  (wrote:U32.t)
  (entries' : _)
  (out_bytes' : _)
: Tot vprop
=        A.pts_to (EXT.gtake output) full_perm out_bytes'
           `star`
         pure (M.verify_post_success_pure_inv
            tid
            entries
            log_bytes
            out_bytes
            read
            wrote
            entries'
            out_bytes')

[@@__reduce__]
let verify_post_some_m_success
  (tid:U16.t)
  (log_perm:perm)
  (log_bytes: AT.bytes)
  (len: U32.t)
  (input: EXT.extern_ptr)
  (out_len: U32.t)
  (out_bytes: AT.bytes)
  (output: EXT.extern_ptr)
  (v: option (v:V.verify_result { V.verify_result_complete len v }))
  (sq: squash (check_verify_input tid len input out_len output))
  (t: M.top_level_state)
  (read:U32.t)
  (wrote:U32.t)
: Tot vprop
=
       exists_ (fun entries -> exists_ (fun entries' -> exists_ (fun out_bytes' ->
         verify_post_some_m_success_body tid log_perm log_bytes len input out_len out_bytes output v sq t entries read wrote entries' out_bytes'
       )))

[@@__reduce__]
let verify_post_some_m_failure
  (output: EXT.extern_ptr)
: Tot vprop
= exists_ (fun s -> A.pts_to (EXT.gtake output) full_perm s)

let verify_post_some_m
  (tid:U16.t)
  (log_perm:perm)
  (log_bytes: AT.bytes)
  (len: U32.t)
  (input: EXT.extern_ptr)
  (out_len: U32.t)
  (out_bytes: AT.bytes)
  (output: EXT.extern_ptr)
  (v: option (v:V.verify_result { V.verify_result_complete len v }))
  (t: M.top_level_state)
: Tot vprop
= match v with
  | Some (V.Verify_success read wrote) ->
    if check_verify_input tid len input out_len output
    then
      verify_post_some_m_success tid log_perm log_bytes len input out_len out_bytes output v () t read wrote
    else
      pure False
  | _ -> verify_post_some_m_failure output 

[@@__reduce__]
let verify_post_some
  (tid:U16.t)
  (log_perm:perm)
  (log_bytes: AT.bytes)
  (len: U32.t)
  (input: EXT.extern_ptr)
  (out_len: U32.t)
  (out_bytes: AT.bytes)
  (output: EXT.extern_ptr)
  (v: option (v:V.verify_result { V.verify_result_complete len v }))
: Tot vprop
= 
    exists_ (fun t ->
      handle_pts_to t `star`
      A.pts_to (EXT.gtake input) log_perm log_bytes `star`
      verify_post_some_m tid log_perm log_bytes len input out_len out_bytes output v t
    )

let verify_post
  (tid:U16.t)
  (log_perm:perm)
  (log_bytes: AT.bytes)
  (len: U32.t)
  (input: EXT.extern_ptr)
  (out_len: U32.t)
  (out_bytes: AT.bytes)
  (output: EXT.extern_ptr)
  (res: option (v:V.verify_result { V.verify_result_complete len v }))
: Tot vprop
= verify_post_some tid log_perm log_bytes len input out_len out_bytes output res

val verify_log
               (tid:U16.t)
               (#log_perm:perm)
               (#log_bytes:Ghost.erased AT.bytes)
               (len: U32.t)
               (input: EXT.extern_ptr)
               (out_len: U32.t)
               (#out_bytes:Ghost.erased AT.bytes)
               (output: EXT.extern_ptr)
  : STT (option (v:V.verify_result { V.verify_result_complete len v }))
    (verify_pre log_perm log_bytes input out_bytes output)
    (fun res -> verify_post tid log_perm log_bytes len input out_len out_bytes output res)

val max_certified_epoch
                        (_: unit)
  : STT AEH.max_certified_epoch_result
        emp
        (fun res -> exists_ (fun t ->
          handle_pts_to t `star`
          M.read_max_post t res
        ))
