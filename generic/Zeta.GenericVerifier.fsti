module Zeta.GenericVerifier

open Zeta.App
open Zeta.Time
open Zeta.Record

module S = FStar.Seq

(* identifier type for verifier threads *)
type thread_id = nat

(* The basic "structure" of a verifier specification. We are interested in specifications that
 * satisfy additional properties as described below. *)
noeq
type verifier_spec_base = {

  (* type of the verifier thread local state *)
  vtls_t: Type0;

  (* is the verifier state valid, indicating no verification failures *)
  valid: vtls_t -> bool;

  (* initialize the thread local state for a particular thread id *)
  init: thread_id -> vtls: vtls_t { valid vtls };

  (* generate a invalid state *)
  fail: vtls_t -> vtls: vtls_t {not (valid vtls)};

  (* clock of a verifier thread. *)
  clock: vtls:vtls_t{valid vtls} -> timestamp;

  (* thread_id of the verifier thread; thread_id can be accessed even in a failed state *)
  tid: vtls_t -> thread_id;

  (* type used to identify records (e.g., keys, slots) *)
  slot_t: eqtype;

  (* application specification *)
  app: app_params;

  (* get a record from the store - this could fail and return None *)
  get: slot_t -> vtls: vtls_t {valid vtls} -> option (record app);

  (* update the record in a slot with a new value *)
  put: s: slot_t -> vtls: vtls_t { valid vtls && Some? (get s vtls)} ->
       v: (value_t (Some?.v (get s vtls))) ->
       vtls': vtls_t { let r = Some?.v (get s vtls) in
                       valid vtls' && Some? (get s vtls') &&
                       Some?.v (get s vtls') = update r v };

  (* implementation of merkle add *)
  addm: record app -> slot_t -> slot_t -> vtls: vtls_t { valid vtls } -> vtls_t;

  (* implementation of blum add *)
  addb: record app -> slot_t -> timestamp -> thread_id -> vtls: vtls_t { valid vtls } -> vtls_t;

  (* implementation of merkle evict *)
  evictm: slot_t -> slot_t -> vtls: vtls_t { valid vtls } -> vtls_t;

  (* implementation of blum evict *)
  evictb: slot_t -> timestamp -> vtls: vtls_t { valid vtls } -> vtls_t;

  (* implementation of blum evict for records added using merkle *)
  evictbm: slot_t -> slot_t -> timestamp -> vtls: vtls_t { valid vtls } -> vtls_t;

  nextepoch: vtls: vtls_t { valid vtls } -> vtls_t;

  verifyepoch: vtls: vtls_t { valid vtls } -> vtls_t;
}

type verifier_log_entry (vspec: verifier_spec_base) =
  | AddM: r: record vspec.app -> s: vspec.slot_t -> s': vspec.slot_t -> verifier_log_entry vspec
  | AddB: r: record vspec.app -> s: vspec.slot_t -> t: timestamp -> tid: thread_id -> verifier_log_entry vspec


(*
(* clock is monotonic property *)
let clock_monotonic_prop (vspec: verifier_spec_base) =
  forall (b: builtin). forall (p: vspec.param_t b). forall (vtls: vspec.vtls_t {vspec.valid vtls}).
    {:pattern vspec.impl b p vtls }
    let clock_pre = vspec.clock vtls in
    let vtls_post = vspec.impl b p vtls in
    vspec.valid vtls_post ==> (let clock_post = vspec.clock vtls_post in
                                  clock_pre `ts_leq` clock_post)

(* thread_id is constant *)
let thread_id_constant_prop (vspec: verifier_spec_base) =
  forall (b: builtin). forall (p: vspec.param_t b). forall (vtls: vspec.vtls_t {vspec.valid vtls}).
    {:pattern vspec.impl b p vtls }
    let tid_pre = vspec.tid vtls in
    let tid_post = vspec.tid (vspec.impl b p vtls) in
    tid_pre = tid_post


let verifier_log vspec = S.seq (verifier_log_entry vspec)

let verify_step #vspec (vtls: vspec.vtls_t) (e: verifier_log_entry vspec) =
  if not (vspec.valid vtls) then vtls
  else
  match e with
  | Builtin b p -> vspec.impl b p vtls

  | App f p i ->
    let inp = vspec.appfn_inout i vtls in
    let fn = appfn f in
    (* unable to construct input records: fail *)
    if inp = None then vspec.fail vtls
    else
      admit()
*)
