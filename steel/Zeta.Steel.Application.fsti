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

/// A parser for a application record, a key/value pair
val record_parser : Parser.parser (key_type & value_type)

val vtls : Type0
val vtls_inv (_:vtls) : vprop

let app_records #adm (fsig:A.fn_sig adm) =
  recs:Seq.seq (A.app_record adm) {
    Seq.length recs == fsig.arity /\
    A.distinct_keys recs
  }

let app_values_nullable #adm (fsig:A.fn_sig adm) =
  recs:Seq.seq (A.app_value_nullable adm) {
    Seq.length recs == fsig.arity
  }

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
      (vtls:vtls)
  (* if success, returns the number of bytes written in the output log *)
   : Steel (option U32.t)
      (Array.varray log_array `star`
       Array.varray out `star`
       vtls_inv vtls)
      (fun x ->
        Array.varray log_array `star`
        Array.varray out `star`
        vtls_inv vtls)
      (requires fun _ -> True)
      (ensures fun h0 res h1 ->
        let out_bytes_initial = Array.asel out h0 in
        let out_bytes = Array.asel out h1 in
        let log_bytes = Array.asel log_array h0 in
        let arg_bytes = Parser.slice log_bytes log_offset args_len in
        Array.asel log_array h0 == Array.asel log_array h1 /\
        Seq.slice out_bytes_initial 0 (U32.v out_offset)
          == Seq.slice out_bytes 0 (U32.v out_offset) /\
       (match res with
        | None -> True //underspecify failure
        | Some out_bytes_written ->
          Parser.len_offset_slice_ok out out_len out_offset out_bytes_written /\ (
          let written_bytes = Parser.slice out_bytes out_offset out_bytes_written in
          let fsig = Map.sel aprm.A.tbl fid in
          let arg_t = A.interp_code aprm.A.adm fsig.farg_t in
          let res_t = A.interp_code aprm.A.adm fsig.fres_t in
          exists (arg:arg_t)
            (recs_in:app_records fsig)
            (recs_out:app_values_nullable fsig)
            (v:res_t).
              Parser.parse_spec arg_bytes (arg, recs_in) /\
              Parser.parse_spec written_bytes v /\
              fsig.f arg recs_in == (A.Fn_success, v, recs_out) /\
              True (* some way to say that the recs_out were written back to the vtls *)
          )))
