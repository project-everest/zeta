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
open Zeta.Steel.ApplicationTypes
open Steel.FractionalPermission
open Steel.Effect
module A = Zeta.App
module Parser = Zeta.Steel.Parser
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Array = Steel.Array
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
      (fid: A.appfn_id aprm)
      (* The position in the log where the arguments of the function live *)
      (log_len:U32.t)
      (log_offset:U32.t)
      (args_len:U32.t)
      (log_array:Parser.byte_array {
        Parser.len_offset_slice_ok log_array log_len log_offset args_len
       })
      (* The position in the output log in which to write the results, if any *)
      (out_len:U32.t)
      (out_offset:U32.t)
      (out:Parser.byte_array {
        Parser.len_offset_ok out out_len out_offset
       })
      (* The state of the verifier, with pointers to the store etc. *)
      (vtls:V.thread_state_t)
  (* if success, returns the number of bytes written in the output log *)
   : Steel (option U32.t)
      (V.thread_state_inv vtls `star` (
       Array.varray log_array `star`
       Array.varray out)
       )
      (fun x ->
        V.thread_state_inv vtls `star` (
        Array.varray log_array `star`
        Array.varray out))
      (requires fun _ -> True)
      (ensures fun h0 res h1 ->
        let out_bytes_initial = Array.asel out h0 in
        let out_bytes = Array.asel out h1 in
        let log_bytes = Array.asel log_array h0 in
        let arg_bytes = Parser.slice log_bytes log_offset args_len in
        let tsm0 = V.value_of vtls (focus_rmem h0 _) in
        let tsm1 = V.value_of vtls (focus_rmem h0 _) in
        let app_payload : runApp_payload =
            { fid = fid;
              rest = { len = args_len;
                       ebytes = arg_bytes } }
        in
        Array.asel log_array h0 == Array.asel log_array h1 /\
        Seq.slice out_bytes_initial 0 (U32.v out_offset)
          == Seq.slice out_bytes 0 (U32.v out_offset) /\
        tsm1 == M.runapp tsm0 app_payload /\
        True //TODO: specify outputs, res etc.
        )
