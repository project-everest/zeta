module Zeta.Steel.SafeMain

module M = Zeta.Steel.Main
open Steel.ST.Util

val handle_pts_to
  (ts: M.top_level_state)
: Tot vprop

[@@__reduce__]
let init_post_true : vprop =
  exists_ (fun ts ->
    handle_pts_to ts `star`
    M.core_inv ts `star`
    M.all_logs ts (Map.const (Some Seq.empty))
  )

let init_post (b: bool) : Tot vprop =
  if b
  then init_post_true
  else emp

val init (_: unit) : STT bool
  emp
  (fun b -> init_post b)

module AEH = Zeta.Steel.AggregateEpochHashes
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module U = Zeta.Steel.Util
module V = Zeta.Steel.Verifier
module A = Steel.ST.Array
module AT = Zeta.Steel.ApplicationTypes

val verify_log
               (#t:Ghost.erased M.top_level_state)
               (tid:_)
               (#entries:Ghost.erased AEH.log)
               (#log_perm:perm)
               (#log_bytes:Ghost.erased AT.bytes)
               (len: U32.t { len <> 0ul })
               (input:U.larray U8.t len)
               (out_len: U32.t)
               (#out_bytes:Ghost.erased AT.bytes)
               (output:U.larray U8.t out_len)
  : STT (option (v:V.verify_result { V.verify_result_complete len v }))
    (handle_pts_to t `star`
     M.core_inv t `star`
     A.pts_to input log_perm log_bytes `star`
     A.pts_to output full_perm out_bytes `star`
     M.log_of_tid t tid entries)
    (fun res ->
       handle_pts_to t `star`
       M.verify_post t tid entries log_perm log_bytes len input out_len out_bytes output res)

val max_certified_epoch
                        (#t:Ghost.erased M.top_level_state)
                        (_: unit)
  : STT AEH.max_certified_epoch_result
        (handle_pts_to t)
        (fun res ->
           handle_pts_to t `star`
           M.read_max_post t res)
