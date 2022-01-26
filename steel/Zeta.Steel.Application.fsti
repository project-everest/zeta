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
module App = Zeta.App
module Parser = Zeta.Steel.Parser
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module A = Steel.ST.Array
module M = Zeta.Steel.ThreadStateModel
module V = Zeta.Steel.VerifierTypes
open Zeta.Steel.FormatsManual
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
      (* fid: The id of the function to run *)
      (fid: App.appfn_id aprm)
      (* The position in the log where the arguments of the function live *)
      (#log_perm:perm)
      (#log_bytes:Ghost.erased bytes)
      (log_len:U32.t)
      (log_offset:U32.t)
      (args_len:U32.t { U32.v args_len < 2147483648 })
      (log_array:Parser.byte_array {
        Seq.length log_bytes == U32.v log_len /\
        Parser.len_offset_slice_ok log_array log_len log_offset args_len
       })
      (* The position in the output log in which to write the results, if any *)
      (#out_bytes: Ghost.erased bytes)
      (out_len:U32.t)
      (out_offset:U32.t)
      (out:Parser.byte_array {
        Parser.len_offset_ok out out_len out_offset
       })
      (* The state of the verifier, with pointers to the store etc. *)
      (#tsm:M.thread_state_model)
      (t:V.thread_state_t)
  (* if success, returns the number of bytes written in the output log *)
   : STT (option U32.t)
      (V.thread_state_inv t tsm `star`
       A.pts_to log_array log_perm log_bytes `star`
       A.pts_to out full_perm out_bytes)
      (fun res ->
        A.pts_to log_array log_perm log_bytes `star`
        (match res with
         | None ->
           exists_ (V.thread_state_inv t) `star`
           exists_ (A.pts_to out full_perm)
         | Some n_out ->
           exists_ (fun tsm' ->
           exists_ (fun out_bytes' ->
            V.thread_state_inv t tsm' `star`
            A.pts_to out full_perm (out_bytes `Seq.append` out_bytes') `star`
            pure (
              let arg_bytes = Parser.slice log_bytes log_offset args_len in
              let app_payload : runApp_payload =
              { fid = fid;
                rest = { len = args_len;
                         ebytes = arg_bytes } }
              in
              tsm' == M.runapp tsm app_payload /\
              out_bytes' == M.bytes_of_app_results (M.delta_app_results tsm tsm') /\
              U32.v n_out == Seq.length out_bytes')
            ))))
