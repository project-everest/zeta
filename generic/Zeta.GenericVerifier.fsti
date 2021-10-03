module Zeta.GenericVerifier

open Zeta.App
open Zeta.AppSimulate
open Zeta.Time
open Zeta.MultiSetHashDomain
open Zeta.Record

module S = FStar.Seq
module SA = Zeta.SeqAux
module MSD = Zeta.MultiSetHashDomain

(* identifier type for verifier threads *)
let thread_id = Zeta.Thread.thread_id

(* The basic "structure" of a verifier specification. We are interested in specifications that
 * satisfy additional properties as described below. *)
noeq
type verifier_spec_base = {

  (* type of the verifier thread local state *)
  vtls_t: Type0;

  (* is the verifier state valid, indicating no verification failures *)
  valid: vtls_t -> bool;

  (* generate a invalid state *)
  fail: vtls_t -> vtls: vtls_t {not (valid vtls)};

  (* clock of a verifier thread. *)
  clock: vtls:vtls_t{valid vtls} -> timestamp;

  (* thread_id of the verifier thread; thread_id can be accessed even in a failed state *)
  tid: vtls_t -> thread_id;

  (* initialize the thread local state for a particular thread id *)
  init: t:thread_id -> vtls: vtls_t { valid vtls /\ tid vtls = t };

  (* type used to identify records (e.g., keys, slots) *)
  slot_t: eqtype;

  (* application specification *)
  app: app_params;

  (* get a record from the store - this could fail and return None *)
  get: slot_t -> vtls: vtls_t {valid vtls} -> option (record app);

  (* update the record in a slot with a new value *)
  puts: vtls: vtls_t { valid vtls } ->
        ss: S.seq slot_t ->
        ws: S.seq (app_value_nullable app.adm) ->
        vtls': vtls_t { valid vtls };

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
  | EvictM: s: vspec.slot_t -> s': vspec.slot_t -> verifier_log_entry vspec
  | EvictB: s: vspec.slot_t -> t: timestamp -> verifier_log_entry vspec
  | EvictBM: s: vspec.slot_t -> s': vspec.slot_t -> t: timestamp -> verifier_log_entry vspec
  | NextEpoch: verifier_log_entry vspec
  | VerifyEpoch: verifier_log_entry vspec
  | RunApp: f: appfn_id vspec.app ->
            p: appfn_arg f ->
            rs: S.seq (vspec.slot_t) ->
            verifier_log_entry vspec

let is_appfn #vspec (e: verifier_log_entry vspec)
  = RunApp? e

let param_len #vspec (e: verifier_log_entry vspec{is_appfn e})
  = let RunApp _ _ rs = e in
    S.length rs

let is_internal #vspec (e: verifier_log_entry vspec)
  = not (is_appfn e)

let is_blum_add #vspec (e: verifier_log_entry vspec) = AddB? e

let blum_add_timestamp #vspec (e: verifier_log_entry vspec {is_blum_add e})
  : timestamp
  = match e with
    | AddB _ _ t _ -> t

let is_evict #vspec (e: verifier_log_entry vspec): bool =
  match e with
  | EvictM _ _ -> true
  | EvictB _ _ -> true
  | EvictBM _ _ _ -> true
  | _ -> false

let evict_slot #vspec (e: verifier_log_entry vspec{is_evict e})
  = match e with
    | EvictM s _ -> s
    | EvictB s _ -> s
    | EvictBM s _ _ -> s

let is_blum_evict #vspec (e: verifier_log_entry vspec) =
  match e with
  | EvictB _ _ -> true
  | EvictBM _ _ _ -> true
  | _ -> false

let blum_evict_timestamp #vspec (e: verifier_log_entry vspec {is_blum_evict e})
  = match e with
    | EvictB _ t -> t
    | EvictBM _ _ t -> t

let is_merkle_evict #vspec (e:verifier_log_entry vspec): bool =
  match e with
  | EvictM _ _ -> true
  | _ -> false

let is_add #vspec (e: verifier_log_entry vspec)
  = match e with
    | AddM _ _ _ -> true
    | AddB _ _ _ _ -> true
    | _ -> false

let add_record #vspec (e: verifier_log_entry vspec {is_add e})
  = match e with
    | AddM r _ _ -> r
    | AddB r _ _ _ -> r

let add_slot #vspec (e: verifier_log_entry vspec {is_add e})
  = match e with
    | AddM _ s _ -> s
    | AddB _ s _ _ -> s

let involves_ancestor #vspec (e: verifier_log_entry vspec)
  : bool
  = match e with
    | AddM _ _ _ -> true
    | EvictM _ _ -> true
    | EvictBM _ _ _ -> true
    | _ -> false

let ancestor_slot #vspec (e: verifier_log_entry vspec {involves_ancestor e})
  = match e with
    | AddM _ _ k -> k
    | EvictM _ k -> k
    | EvictBM _ k _ -> k

let is_ancestor_evict #vspec (e: verifier_log_entry vspec)
  = is_evict e && involves_ancestor e

(* does a slot contain an app key *)
let contains_app_key
  (#vspec: verifier_spec_base)
  (vtls: vspec.vtls_t {vspec.valid vtls})
  (s: vspec.slot_t)
  : bool
  = Some? (vspec.get s vtls)  &&
    (let gk, _ = Some?.v (vspec.get s vtls) in
     Zeta.GenKey.AppK? gk)

(* from a slot containing an app key, get the app record *)
let to_app_record
  (#vspec: verifier_spec_base)
  (vtls: vspec.vtls_t {vspec.valid vtls})
  (s: vspec.slot_t {contains_app_key vtls s})
  : app_record vspec.app.adm
  = let open Zeta.GenKey in
    let open Zeta.Record in
    let AppK ak, AppV av = Some?.v (vspec.get s vtls) in
    ak, av

let to_app_key
  (#vspec: verifier_spec_base)
  (vtls: vspec.vtls_t {vspec.valid vtls})
  (s: vspec.slot_t {contains_app_key vtls s})
  : app_key vspec.app.adm
  = let open Zeta.GenKey in
    let open Zeta.Record in
    let AppK ak, _ = Some?.v (vspec.get s vtls) in
    ak

let contains_only_app_keys
  (#vspec:_) (vtls: vspec.vtls_t{vspec.valid vtls}) (ss: S.seq vspec.slot_t)
  = forall i. contains_app_key vtls (S.index ss i)

let contains_distinct_app_keys
  (#vspec:_) (vtls: vspec.vtls_t{vspec.valid vtls}) (ss: S.seq vspec.slot_t)
  = contains_only_app_keys vtls ss /\
    (forall i1 i2. i1 <> i2 ==> to_app_key vtls (S.index ss i1) <> to_app_key vtls (S.index ss i2))

val contains_distinct_app_keys_comp
  (#vspec:_) (vtls: vspec.vtls_t{vspec.valid vtls}) (ss: S.seq vspec.slot_t)
  : b:bool {b <==> contains_distinct_app_keys vtls ss}

let read
  (#vspec:_)
  (vtls: vspec.vtls_t{vspec.valid vtls})
  (ss: S.seq vspec.slot_t{contains_distinct_app_keys vtls ss})
  (i: SA.seq_index ss)
  = to_app_record vtls (S.index ss i)

let reads
  (#vspec: verifier_spec_base)
  (vtls: vspec.vtls_t {vspec.valid vtls})
  (ss: S.seq vspec.slot_t {contains_distinct_app_keys vtls ss})
  = S.init (S.length ss) (read vtls ss)

let verify_step (#vspec: verifier_spec_base)
                (e: verifier_log_entry vspec)
                (vtls: vspec.vtls_t): vspec.vtls_t =
  if not (vspec.valid vtls) then vtls
  else
    match e with
    | AddM r s s' -> vspec.addm r s s' vtls
    | AddB r s t tid -> vspec.addb r s t tid vtls
    | EvictM s s' -> vspec.evictm s s' vtls
    | EvictB s t -> vspec.evictb s t vtls
    | EvictBM s s' t -> vspec.evictbm s s' t vtls
    | NextEpoch -> vspec.nextepoch vtls
    | VerifyEpoch -> vspec.verifyepoch vtls
    | RunApp f p ss ->
      (* slots do not point to distinct keys *)
      if not (contains_distinct_app_keys_comp vtls ss) then vspec.fail vtls
      (* fails arity requirement *)
      else if S.length ss <> appfn_arity f then vspec.fail vtls

      else
        (* the app function to run *)
        let fn = appfn f in
        (* the records specified by ss *)
        let rs = reads vtls ss in
        (* run the app function *)
        let rc, _, ws = fn p rs in
        (* if app function returns failure, verifier goes to failed state *)
        if rc = Fn_failure then vspec.fail vtls
        (* update the verifier store with the writes of the function *)
        else vspec.puts vtls ss ws

let appfn_result #vspec
  (e: verifier_log_entry vspec{is_appfn e})
  (vtls: vspec.vtls_t {vspec.valid (verify_step e vtls)})
  : appfn_call_res vspec.app
  = assert(vspec.valid vtls);
    match e with
    | RunApp f p ss ->
      let fn = appfn f in
      let rs = reads vtls ss in
      let _,o,_ = fn p rs in
      {fid_cr = f; arg_cr = p; inp_cr = rs; res_cr = o}

let verifier_failure_propagating (#vspec: _) (e: verifier_log_entry vspec) (vtls: vspec.vtls_t):
  Lemma (requires (vspec.valid (verify_step e vtls)))
        (ensures (vspec.valid vtls)) = ()

(* clock is monotonic property *)
let clock_monotonic_prop (vspec: verifier_spec_base) =
  forall (e: verifier_log_entry vspec) (vtls: vspec.vtls_t).
    {:pattern verify_step e vtls}
    let vtls_post = verify_step e vtls in
    vspec.valid vtls_post ==> (let clock_pre = vspec.clock vtls in
                               let clock_post = vspec.clock vtls_post in
                               clock_pre `ts_leq` clock_post)

(* thread_id is constant *)
let thread_id_constant_prop (vspec: verifier_spec_base) =
  forall (e: verifier_log_entry vspec) (vtls: vspec.vtls_t).
    {:pattern verify_step e vtls}
    let tid_pre = vspec.tid vtls in
    let tid_post = vspec.tid (verify_step e vtls) in
    tid_pre = tid_post

(* a slot is non-empty before evict and empty after, if the verify succeeds *)
let evict_prop (vspec: verifier_spec_base) =
  forall (e: verifier_log_entry vspec) (vtls: vspec.vtls_t).
    {:pattern verify_step e vtls}
    let vtls' = verify_step e vtls in
    is_evict e ==>
    vspec.valid vtls' ==>
    Some? (vspec.get (evict_slot e) vtls) /\
    None? (vspec.get (evict_slot e) vtls')

(* a slot is empty before add and non-empty after, if the add succeeds *)
let add_prop (vspec: verifier_spec_base) =
  forall (e: verifier_log_entry vspec) (vtls: vspec.vtls_t).
    {:pattern verify_step e vtls}
    let vtls' = verify_step e vtls in
    is_add e ==>
    vspec.valid vtls' ==>
    None? (vspec.get (add_slot e) vtls) /\
    Some? (vspec.get (add_slot e) vtls')

(* the timestamp of blum add is lesser than the clock after processing the entry *)
let addb_prop (vspec: verifier_spec_base)
  = forall (e: verifier_log_entry vspec) (vtls: vspec.vtls_t).
    {:pattern verify_step e vtls}
    let vtls' = verify_step e vtls in
    is_blum_add e ==>
    vspec.valid vtls' ==>
    blum_add_timestamp e `ts_lt` vspec.clock vtls'

let evictb_prop (vspec: verifier_spec_base)
  = forall (e: verifier_log_entry vspec) (vtls: vspec.vtls_t).
    {:pattern verify_step e vtls}
    let vtls' = verify_step e vtls in
    is_blum_evict e ==>
    vspec.valid vtls' ==>
    (let clock_pre = vspec.clock vtls in
     let clock_post = vspec.clock vtls' in
     clock_pre `ts_lt` clock_post /\
     clock_post = blum_evict_timestamp e)

let verifier_log vspec = S.seq (verifier_log_entry vspec)

let rec verify #vspec (tid: thread_id) (l: verifier_log vspec):
  Tot (vspec.vtls_t)
  (decreases (S.length l)) =
  let n = S.length l in
  if n = 0 then vspec.init tid
  else
    let vtls' = verify tid (SA.prefix l (n-1)) in
    verify_step (S.index l (n-1)) vtls'

let verifier_spec = vspec:verifier_spec_base
    {clock_monotonic_prop vspec /\ thread_id_constant_prop vspec /\ evict_prop vspec /\ add_prop vspec /\
     addb_prop vspec /\ evictb_prop vspec}
