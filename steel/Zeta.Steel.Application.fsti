module Zeta.Steel.Application
(**
 * This interface will be instantiated by each Zeta application
 * It requires:
 *
 *    - A function to parse keys and values from raw bytes
 *
 *    - A function to run each application-specific state transition
 *      with specs relating it to the high-level model of a Zeta
 *      application
 **)
open Steel.ST.Util
open Zeta.Steel.ApplicationTypes
open Zeta.Steel.Util
module Parser = Zeta.Steel.Parser
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module A = Steel.ST.Array
module M = Zeta.Steel.ThreadStateModel
module V = Zeta.Steel.VerifierTypes
open Zeta.Steel.FormatsManual

let delta_out_bytes (tsm tsm':M.thread_state_model)
  = M.bytes_of_app_results (M.delta_app_results tsm tsm')

let delta_out_bytes_idem (tsm:M.thread_state_model)
  : Lemma (delta_out_bytes tsm tsm == Seq.empty)
          [SMTPat (delta_out_bytes tsm tsm)]
  = admit()

let delta_out_bytes_not_runapp (tsm:M.thread_state_model)
                               (le:log_entry { not (RunApp? le) })
  : Lemma (delta_out_bytes tsm (M.verify_step_model tsm le) == Seq.empty)
          [SMTPat (delta_out_bytes tsm (M.verify_step_model tsm le))]
  = admit()

let delta_out_bytes_trans (tsm tsm1:M.thread_state_model)
                          (le:log_entry)
  : Lemma (ensures
              delta_out_bytes tsm (M.verify_step_model tsm1 le) ==
              Seq.append (delta_out_bytes tsm tsm1)
                         (delta_out_bytes tsm1 (M.verify_step_model tsm1 le)))
  = admit()

let split3 (s:Seq.seq U8.t)
           (from:U32.t { U32.v from <= Seq.length s})
           (to:U32.t { U32.v to <= Seq.length s - U32.v from })
  = Seq.slice s 0 (U32.v from),
    Seq.slice s (U32.v from) (U32.v from + U32.v to),
    Seq.slice s (U32.v from + U32.v to) (Seq.length s)

let n_out_bytes (tsm tsm': M.thread_state_model)
                (out_offset:U32.t)
                (n_out:U32.t)
                (out_bytes_init:Seq.seq U8.t)
                (out_bytes_final:Seq.seq U8.t)
  : prop
  = Seq.length out_bytes_init == Seq.length out_bytes_final /\
    U32.v out_offset <= Seq.length out_bytes_init /\
    U32.v n_out <= Seq.length out_bytes_init - U32.v out_offset /\
    (let pfx, _, sfx = split3 out_bytes_init out_offset n_out in
     let pfx', s, sfx' = split3 out_bytes_init out_offset n_out in
     pfx `Seq.equal` pfx' /\
     sfx `Seq.equal` sfx' /\
     s `Seq.equal` delta_out_bytes tsm tsm')

type verify_runapp_result =
  | Run_app_parsing_failure: verify_runapp_result
  | Run_app_verify_failure: verify_runapp_result
  | Run_app_success: wrote:U32.t -> verify_runapp_result

let verify_runapp_entry_post (tsm:M.thread_state_model)
                             (t:V.thread_state_t)
                             (pl: runApp_payload)
                             (out_bytes:bytes)
                             (out_offset:U32.t)
                             (out:A.array U8.t)
                             ([@@@smt_fallback] res:verify_runapp_result)
  : vprop
  = match res with
    | Run_app_parsing_failure
    | Run_app_verify_failure ->
      //failure, but leaves state unchanged
      V.thread_state_inv t tsm `star`
      array_pts_to out out_bytes

    | Run_app_success wrote ->
      exists_ (fun (out_bytes':Seq.seq U8.t) ->
        (let tsm' = M.verify_step_model tsm (RunApp pl) in
         V.thread_state_inv t tsm' `star` //tsm' is the new state of the thread
         array_pts_to out out_bytes' `star`
         pure (n_out_bytes tsm tsm' out_offset wrote out_bytes out_bytes')))

(**
    Running an application-specific state transition function,
    identified by `fid`.

    The signature of this function is carefully chosen to enabled
    extraction to a C function prototype in a standalone .h file. This
    allows us to separate implement and compile Zeta application
    instances and link them at the C level with rest of the Zeta
    framework.
*)
val run_app_function
      (* The position in the log where the arguments of the function live *)
      (#log_perm:perm)
      (#log_bytes:Ghost.erased bytes)
      (log_len: Ghost.erased U32.t)
      (pl: runApp_payload)
      (pl_pos:U32.t)
      (log_array:larray U8.t log_len {
        U32.v pl_pos + U32.v pl.rest.len <= Seq.length log_bytes /\
        U32.v log_len == Seq.length log_bytes /\
        Ghost.reveal pl.rest.ebytes == Seq.slice log_bytes (U32.v pl_pos) (U32.v pl_pos + U32.v pl.rest.len)
       })
      (* The position in the output log in which to write the results, if any *)
      (#out_bytes: Ghost.erased bytes)
      (out_len:U32.t)
      (out_offset:U32.t{
        U32.v out_offset <= Seq.length out_bytes
       })
      (out:larray U8.t out_len)
      (* The state of the verifier, with pointers to the store etc. *)
      (#tsm:M.thread_state_model)
      (t:V.thread_state_t)
  (* if success, returns the number of bytes written in the output log *)
   : STT verify_runapp_result
      (V.thread_state_inv t tsm `star`
       A.pts_to log_array log_perm log_bytes `star`
       A.pts_to out full_perm out_bytes)
      (fun res ->
        A.pts_to log_array log_perm log_bytes `star`
        verify_runapp_entry_post tsm t pl out_bytes out_offset out res)

(** A function to map application keys to base keys *)
module LE = Zeta.Steel.LogEntry.Types
val key_type_to_base_key (k:key_type)
  : STT (b:LE.base_key {  b == Zeta.Steel.KeyUtils.lower_base_key (aprm.keyhashfn k) })
    emp (fun _ -> emp)
