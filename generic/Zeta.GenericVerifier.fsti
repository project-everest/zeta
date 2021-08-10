module Zeta.GenericVerifier

open Zeta.App
open Zeta.Time
open Zeta.Record

module S = FStar.Seq

(*
 * Verifier built-in methods
 *
 * A verifier thread supports the following built-in methods that can be used
 * to (a) add records to its internal store (b) evict records from its internal
 * store; and (c) trigger epoch transitions.
 *
 * These are different from application methods that implement application-specific
 * state machine transitions.
 *)
type builtin =
  | AddM                    (* Add a record using Merkle verification *)
  | EvictM                  (* Evict a record, while protecting it using Merkle *)
  | AddB                    (* Add a record using Blum verification *)
  | EvictB                  (* Evict a record using Blum protection *)
  | EvictBM                 (* Evict a record added using Merkle using Blum protection *)
  | NextEpoch               (* Transition the verifier thread clock to next epoch *)
  | VerifyEpoch             (* *)

(* subset of builtins that add a record *)
let is_add m =
  match m with
  | AddM
  | AddB -> true
  | _ -> false

(* subset of builtins that evict a record *)
let is_evict m =
  match m with
  | EvictM
  | EvictB
  | EvictBM -> true
  | _ -> false

(* subset of builtins that manage epochs *)
let is_epoch_bookkeeping m =
  match m with
  | NextEpoch
  | VerifyEpoch -> true
  | _ -> false

(* identifier type for verifier threads *)
type thread_id = nat

(* The basic "structure" of a verifier specification. We are interested in specifications that
 * satisfy additional properties as described below. *)
noeq
type verifier_spec_base = {
  (* type of the verifier thread local state *)
  vtls_t: Type0;

  (* is the verifier state valid? verification failures take the verifier state to an invalid state. *)
  valid: vtls_t -> bool;

  (* clock of a verifier thread. *)
  clock: v:vtls_t{valid v} -> timestamp;

  (* thread_id of the verifier thread *)
  tid: vtls_t -> thread_id;

  (* input parameter types of builtin methods *)
  param_t: builtin -> eqtype;

  (* implementations of the builtin methods *)
  impl: b: builtin -> param_t b -> v:vtls_t{valid v} -> vtls_t;

  (* for add-builtins, extract the added record from the parameters *)
  add_rec: b: builtin {is_add b} -> param_t b -> record;

  (* for evict builtins, extract the evicted record from the parameters and verifier state *)
  evict_rec: b: builtin {is_evict b} ->
             p: param_t b ->
             v:vtls_t{valid v && valid (impl b p v)} ->
             record;

  (* application specification *)
  app: app_params;

  (* initialize the thread state *)
  init: thread_id -> v: vtls_t {valid v};

  get_param_t: eqtype;
}

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

type verifier_log_entry (vspec: verifier_spec_base) =
  | Builtin: b: builtin -> p: vspec.param_t b -> verifier_log_entry vspec
  | App: f: appfn_id vspec.app -> p: appfn_arg f -> verifier_log_entry vspec

let verifier_log vspec = S.seq (verifier_log_entry vspec)

let verify_step #vspec (vtls: vspec.vtls_t) (e: verifier_log_entry vspec) =
  if not (vspec.valid vtls) then vtls
  else
  match e with
  | Builtin b p -> vspec.impl b p vtls
  | App f p -> admit()
