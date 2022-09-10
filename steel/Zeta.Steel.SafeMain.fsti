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

// NOTE: I don't need to expose these, but I choose to do so
// (especially the elim part) because I am reusing verify_post which
// has core_inv in it.

val handle_pts_to_core_inv_intro
  (#opened: _)
  (ts: M.top_level_state)
: STGhostT unit opened
    (handle_pts_to ts)
    (fun _ -> handle_pts_to ts `star` M.core_inv ts)

val handle_pts_to_core_inv_elim
  (#opened: _)
  (ts: M.top_level_state)
: STGhostT unit opened
    (handle_pts_to ts `star` M.core_inv ts)
    (fun _ -> handle_pts_to ts)

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

[@@__reduce__]
let init_post_true (ts: M.top_level_state) : vprop =
  M.all_logs ts (Map.const (Some Seq.empty))

let init_post (b: bool) (ts: M.top_level_state) : Tot vprop =
  if b
  then init_post_true ts
  else emp

val init (_: unit) : STT bool
  emp
  (fun b ->
    exists_ (fun ts ->
      handle_pts_to ts `star`
      init_post b ts
  ))

let verify_result (len: U32.t) = option (option (v:V.verify_result { V.verify_result_complete len v }))

[@__reduce__]
let verify_pre
    (log_perm:perm)
    (log_bytes: AT.bytes)
    (input: EXT.extern_ptr U8.t)
    (out_bytes: AT.bytes)
    (output: EXT.extern_ptr U8.t)
: Tot vprop
=
     A.pts_to (EXT.gtake input) log_perm log_bytes `star`
     A.pts_to (EXT.gtake output) full_perm out_bytes

inline_for_extraction
let check_verify_input
  (tid: U16.t)
  (len: U32.t) // { len <> 0ul })
  (input: EXT.extern_ptr U8.t) // U.larray U8.t len)
  (out_len: U32.t)
  (output: EXT.extern_ptr U8.t) // U.larray U8.t out_len)
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
  (len: U32.t) // { len <> 0ul })
  (input: EXT.extern_ptr U8.t) // U.larray U8.t len)
  (out_len: U32.t)
  (out_bytes: AT.bytes)
  (output: EXT.extern_ptr U8.t) // U.larray U8.t out_len)
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
  (len: U32.t) // { len <> 0ul })
  (input: EXT.extern_ptr U8.t) // U.larray U8.t len)
  (out_len: U32.t)
  (out_bytes: AT.bytes)
  (output: EXT.extern_ptr U8.t) // U.larray U8.t out_len)
  (v: option (v:V.verify_result { V.verify_result_complete len v }))
  (sq: squash (check_verify_input tid len input out_len output))
  (t: M.top_level_state)
  (entries: _)
  (read:U32.t)
  (wrote:U32.t)
: Tot vprop
=
       exists_ (fun entries' -> exists_ (fun out_bytes' ->
         verify_post_some_m_success_body tid log_perm log_bytes len input out_len out_bytes output v sq t entries read wrote entries' out_bytes'
       ))

[@@__reduce__]
let verify_post_some_m_failure
  (output: EXT.extern_ptr U8.t) // U.larray U8.t out_len)
: Tot vprop
= exists_ (fun s -> A.pts_to (EXT.gtake output) full_perm s)

let verify_post_some_m
  (tid:U16.t)
  (log_perm:perm)
  (log_bytes: AT.bytes)
  (len: U32.t) // { len <> 0ul })
  (input: EXT.extern_ptr U8.t) // U.larray U8.t len)
  (out_len: U32.t)
  (out_bytes: AT.bytes)
  (output: EXT.extern_ptr U8.t) // U.larray U8.t out_len)
  (v: option (v:V.verify_result { V.verify_result_complete len v }))
  (sq: squash (check_verify_input tid len input out_len output))
  (t: M.top_level_state)
  (entries: _)
: Tot vprop
= match v with
  | Some (V.Verify_success read wrote) ->
    verify_post_some_m_success tid log_perm log_bytes len input out_len out_bytes output v sq t entries read wrote
  | _ -> verify_post_some_m_failure output 

[@@__reduce__]
let verify_post_some
  (tid:U16.t)
  (log_perm:perm)
  (log_bytes: AT.bytes)
  (len: U32.t) // { len <> 0ul })
  (input: EXT.extern_ptr U8.t) // U.larray U8.t len)
  (out_len: U32.t)
  (out_bytes: AT.bytes)
  (output: EXT.extern_ptr U8.t) // U.larray U8.t out_len)
  (v: option (v:V.verify_result { V.verify_result_complete len v }))
  (sq: squash (check_verify_input tid len input out_len output))
: Tot vprop
= 
    exists_ (fun t -> exists_ (fun entries ->
      handle_pts_to t `star`
      A.pts_to (EXT.gtake input) log_perm log_bytes `star`
      verify_post_some_m tid log_perm log_bytes len input out_len out_bytes output v sq t entries
    ))

let verify_post
  (tid:U16.t)
  (log_perm:perm)
  (log_bytes: AT.bytes)
  (len: U32.t) // { len <> 0ul })
  (input: EXT.extern_ptr U8.t) // U.larray U8.t len)
  (out_len: U32.t)
  (out_bytes: AT.bytes)
  (output: EXT.extern_ptr U8.t) // U.larray U8.t out_len)
  (res: verify_result len)
: Tot vprop
= match res with
  | None -> verify_pre log_perm log_bytes input out_bytes output
  | Some v ->
    if check_verify_input tid len input out_len output
    then verify_post_some tid log_perm log_bytes len input out_len out_bytes output v ()
    else pure False

val verify_log
               (tid:U16.t)
               (#log_perm:perm)
               (#log_bytes:Ghost.erased AT.bytes)
               (len: U32.t)
               (input: EXT.extern_ptr U8.t)
               (out_len: U32.t)
               (#out_bytes:Ghost.erased AT.bytes)
               (output: EXT.extern_ptr U8.t)
  : STT (verify_result len)
    (verify_pre log_perm log_bytes input out_bytes output)
    (fun res -> verify_post tid log_perm log_bytes len input out_len out_bytes output res)

[@@__reduce__]
let max_certified_epoch_post_some
  (res: AEH.max_certified_epoch_result)
: Tot vprop
=
  exists_ (fun t -> handle_pts_to t `star`
    M.read_max_post t res)

let max_certified_epoch_post
  (res: option AEH.max_certified_epoch_result)
: Tot vprop
= match res with
  | None -> emp
  | Some res -> max_certified_epoch_post_some res

val max_certified_epoch
                        (_: unit)
  : STT (option AEH.max_certified_epoch_result)
        emp
        (fun res -> max_certified_epoch_post res)
