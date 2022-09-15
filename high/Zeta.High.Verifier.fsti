module Zeta.High.Verifier

open Zeta.App
open Zeta.Time
open Zeta.Thread
open Zeta.Key
open Zeta.GenKey
open Zeta.Record
open Zeta.HashFunction

module S = FStar.Seq
module SA = Zeta.SeqAux
module GV = Zeta.GenericVerifier
module T = Zeta.Time

(* for records in the store, how were they added? *)
type add_method =
  | MAdd: add_method       (* AddM *)
  | BAdd: add_method         (* AddB *)

let compatible #aprm (k:base_key) (r:record aprm)
  = let kr,_ = r in
    to_base_key kr = k

(* verifier store entry indexed by a key k *)
type vstore_entry (aprm: app_params) (k:base_key) = {
  r:  r:record aprm {compatible k r};
  am: add_method;
}

(* verifier store is a subset of (k,v) records *)
(* we also track how the key was added merkle/blum *)
let store_t (aprm: app_params) = (k:base_key) -> option (vstore_entry aprm k)

(* does the store contain a key *)
let store_contains (#aprm: app_params) (st:store_t aprm) (k:base_key)
  = Some? (st k)

(* lookup the value of a key in the store *)
let stored_value (#aprm: app_params) (st:store_t aprm) (k:base_key {store_contains st k})
  = let _, v = (Some?.v (st k)).r in
    v

let stored_key (#aprm: app_params) (st:store_t aprm) (k:base_key {store_contains st k})
  = let k, _ = (Some?.v (st k)).r in
    k

(* add method of a key in the store *)
let add_method_of (#aprm: app_params) (st:store_t aprm) (k:base_key {store_contains st k})
  = (Some?.v (st k)).am

(* update the store *)
let update_store (#aprm: app_params)
                 (st:store_t aprm)
                 (k:base_key {store_contains st k})
                 (r:record aprm {compatible k r}):
  Tot (st':store_t aprm {store_contains st' k /\ stored_value st' k = (value_of r)})
  = let am = add_method_of st k in
    fun k' -> if k' = k then Some ( { r; am } ) else st k'

(* add a new record to the store *)
let add_to_store (#aprm: app_params)
                 (st:store_t aprm)
                 (r: record aprm)
                 (am:add_method):
  (st':store_t aprm {let k,v = r in
                     let k = to_base_key k in
                     store_contains st' k /\ stored_value st' k = v})
  = let k,_ = r in
    let k = to_base_key k in
    fun k' -> if k' = k then Some ({ r; am }) else st k'

(* evict a key from a store *)
let evict_from_store (#aprm: app_params)
                     (st:store_t aprm)
                     (k:base_key {store_contains st k}) =
  fun k' -> if k' = k then None else st k'

(* per-thread state of the high-level verifier *)
noeq type vtls_t (app: app_params) = {
  (* is the verifier valid *)
  valid: bool;

  (* thread id *)
  tid: thread_id;

  (* clock *)
  clock: timestamp;

  (* last key evicted using blum *)
  last_evict_key: base_key;

  (* verifier store *)
  st: store_t app;
}

let fail (#aprm: app_params) (vtls: vtls_t aprm):
  vtls': vtls_t aprm {not (vtls'.valid)}
  = { valid = false; tid = vtls.tid; clock = vtls.clock; last_evict_key = vtls.last_evict_key; st = vtls.st }

let clock_lek (#app: app_params) (vtls: vtls_t app) = (vtls.clock, vtls.last_evict_key)

(* update the store of a specified verifier thread *)
let update_thread_store
  (#aprm: app_params)
  (vtls:vtls_t aprm {vtls.valid})
  (st:store_t aprm)
  = { valid = vtls.valid; tid = vtls.tid; clock = vtls.clock; last_evict_key = vtls.last_evict_key; st = st  }

let update_thread_clock
  (#aprm: app_params)
  (vtls:vtls_t aprm {vtls.valid})
  (clock: timestamp)
  = { valid = vtls.valid; tid = vtls.tid; clock ; last_evict_key = vtls.last_evict_key; st = vtls.st  }

let update_thread_last_evict_key
  (#aprm: app_params)
  (vtls: vtls_t aprm {vtls.valid})
  (last_evict_key: base_key)
  = { valid = vtls.valid; tid = vtls.tid; clock = vtls.clock ; last_evict_key; st = vtls.st  }

let addm (#aprm: app_params)
         (r:record aprm)
         (k: base_key)
         (k': base_key)
         (vs: vtls_t aprm {vs.valid}):
    GTot (vs':vtls_t aprm {vs'.tid = vs.tid /\ vs'.clock = vs.clock})
  = let st = vs.st in
    let open Zeta.BinTree in
    let open Zeta.Merkle in
    (* the key of the record should be compatible with the "slot" k *)
    if not (compatible k r) then fail vs
    (* check k is a proper desc of k' *)
    else if not (is_proper_desc k k') then fail vs
    (* check store contains k' *)
    else if not (store_contains st k') then fail vs
    (* check store does not contain k *)
    else if store_contains st k then fail vs
    else
      let v = value_of r in
      let v' = to_merkle_value (stored_value st k') in
      let d = desc_dir k k' in
      let dh' = desc_hash v' d in
      let h = hashfn v in
      match dh' with
      | Empty ->
        if is_init_record r
        then
          let v' = update_value v' d k Zeta.Hash.zero false in
          let st = update_store st k' (IntK k', IntV v') in
          let st = add_to_store st r MAdd in
          update_thread_store vs st
        else
          fail vs
      | Desc k2 h2 b2 ->
        if k2 = k
        then
          if h2 = h && b2 = false then
            update_thread_store vs (add_to_store st r MAdd)
          else fail vs
        else if not (is_init_record r) then fail vs
        else if not (is_proper_desc k2 k) then fail vs
        else
          let d2 = desc_dir k2 k in
          let mv = to_merkle_value v in
          let mv = update_value mv d2 k2 h2 b2 in
          let v' = update_value v' d k Zeta.Hash.zero false in
          let st = update_store st k' (IntK k', IntV  v') in
          let st = add_to_store st (IntK k, (IntV mv)) MAdd in
          update_thread_store vs st

(* key k is in store and was added using Merkle *)
let is_instore_madd (#aprm: app_params) (st: store_t aprm) (k: base_key)
  = store_contains st k &&
    add_method_of st k = MAdd

let has_instore_merkle_desc
  (#aprm: app_params)
  (st: store_t aprm)
  (k: base_key {store_contains st k})
  = let open Zeta.Key in
    if is_leaf_key k then false
    else
      let v = to_merkle_value (stored_value st k) in
      let open Zeta.Merkle in
      let open Zeta.BinTree in
      let ld = desc_hash v Left in
      let rd = desc_hash v Right in
      Desc? ld && is_instore_madd st (Desc?.k ld) ||
      Desc? rd && is_instore_madd st (Desc?.k rd)

let evictm (#aprm: app_params)
           (k:base_key)
           (k':base_key)
           (vs: vtls_t aprm  {vs.valid}):
      GTot (vs': vtls_t aprm {vs'.tid = vs.tid /\ vs'.clock = vs.clock})
  = let st = vs.st in
    let open Zeta.BinTree in
    (* check store contains k and k' *)
    if not (store_contains st k && store_contains st k') then fail vs
    else if not (is_proper_desc k k') then fail vs
    else if has_instore_merkle_desc st k then fail vs
    else
      let v' = to_merkle_value (stored_value st k') in
      let v = stored_value st k in
      let d = desc_dir k k' in
      let open Zeta.Merkle in
      let dh' = desc_hash v' d in
      let h = hashfn v in
      match dh' with
      | Empty -> fail vs
      | Desc k2 h2 b2 -> if k2 = k then
                           let v' = update_value v' d k h false in
                           let st = evict_from_store (update_store st k' (IntK k', IntV v')) k in
                           update_thread_store vs st
                        else fail vs

let addb (#aprm: app_params)
         (r:record aprm)
         (k: base_key)
         (t:timestamp)
         (j:thread_id)
         (vs:vtls_t aprm {vs.valid})
         : (vs': vtls_t aprm {vs'.tid = vs.tid /\ vs.clock `ts_leq` vs'.clock })
  = let st = vs.st in
    let open Zeta.BinTree in
    (* the key of the record r has to be k or its hash has to be k (for app records) *)
    if not (compatible k r) then fail vs
    (* never add Root *)
    else if k = Root then fail vs
    (* check store does not contain k *)
    else if store_contains st k then fail vs
    else
      (* updated clock max of current, 1 + t *)
      let clk = T.max vs.clock (next t) in

      (* if clock increases reset last_evict_key to Root, a dummy value *)
      let vs = if vs.clock `ts_lt` clk then update_thread_last_evict_key vs Zeta.BinTree.Root else vs in

      (* update verifier state with new clock *)
      let vs = update_thread_clock vs clk in
      (* add record to store *)
      let st = add_to_store st r BAdd in
      update_thread_store vs st

let evictb_aux (#aprm: app_params)
               (k:base_key)
               (t:timestamp)
               (eam:add_method)
               (vs:vtls_t aprm {vs.valid}): vtls_t aprm
  = let st = vs.st in
    let open Zeta.BinTree in
    if k = Root then fail vs
    else if not (clock_lek vs `Zeta.TimeKey.lt`  (t,k)) then fail vs
    else if not (store_contains st k) then fail vs
    else if add_method_of st k <> eam then fail vs
    else if has_instore_merkle_desc st k then fail vs
    else
      let vs = update_thread_clock vs t in
      let vs = update_thread_last_evict_key vs k in
      let st = evict_from_store st k in
      update_thread_store vs st

let evictb (#aprm: app_params)
           (k:base_key)
           (t:timestamp)
           (vs:vtls_t aprm {vs.valid})
           : (vs': vtls_t aprm {vs'.tid = vs.tid /\ vs.clock `ts_leq` vs'.clock})
  = evictb_aux k t BAdd vs

let evictbm (#aprm: app_params)
            (k:base_key)
            (k':base_key)
            (t:timestamp)
            (vs:vtls_t  aprm {vs.valid})
            : (vs': vtls_t aprm {vs'.tid = vs.tid /\ vs.clock `ts_leq` vs'.clock})
  = let st = vs.st in
    let open Zeta.BinTree in
    if not (store_contains st k') then fail vs
    else if not (is_proper_desc k k') then fail vs
    else if not (store_contains st k) then fail vs
    else if add_method_of st k <> MAdd then fail vs
    else if has_instore_merkle_desc st k then fail vs
    else
      let v' = to_merkle_value (stored_value st k') in
      let d = desc_dir k k' in
      let open Zeta.Merkle in
      let dh' = desc_hash v' d in
      match dh' with
      | Empty ->
        fail vs
      | Desc k2 h2 b2 ->
        if k2 = k && b2 = false then
          let v' = update_value v' d k h2 true in
          let st = update_store st k' (IntK k', IntV v') in
          evictb_aux k t MAdd (update_thread_store vs st)
        else fail vs

let nextepoch (#aprm: app_params) (vs: vtls_t aprm{vs.valid})
    : (vs': vtls_t aprm {vs'.tid = vs.tid /\ vs.clock `ts_leq` vs'.clock})
  = let e = vs.clock.e + 1 in
    let clock = { e; c = 0 } in
    let vs = update_thread_last_evict_key vs Zeta.BinTree.Root in
    update_thread_clock vs clock

let verifyepoch (#aprm: app_params) (vs: vtls_t aprm{vs.valid})
    : (vs': vtls_t aprm {vs'.tid = vs.tid /\ vs.clock `ts_leq` vs'.clock})
  = vs

let empty_store (aprm: app_params): store_t aprm = fun (k:base_key) -> None

(* initialize verifier state *)
let init_thread_state (aprm: app_params) (tid:thread_id): vtls_t aprm =
  let vs = { valid = true; tid; clock = { e=0; c=0 }; last_evict_key = Zeta.BinTree.Root;  st = empty_store aprm } in
  if tid = 0 then
    let st = vs.st in
    let open Zeta.BinTree in
    let st = add_to_store st (IntK Root, init_value (IntK Root)) MAdd in
    update_thread_store vs st
  else vs

(* does a slot contain an app key *)
let contains_app_key (#app:_) (st: store_t app) (k: base_key)
  = store_contains st k &&
    AppK? (stored_key st k)

(* a sequence of base keys contain only appln keys *)
let contains_only_app_keys (#app:_) (st: store_t app) (ks: S.seq base_key)
  = forall i. contains_app_key st (S.index ks i)

let contains_only_app_keys_comp (#app:_) (st: store_t app) (ks: S.seq base_key)
  : b:bool { b <==> contains_only_app_keys st ks }
  = let open Zeta.SeqIdx in
    not (exists_elems_with_prop_comp (fun k -> not (contains_app_key st k)) ks)

let puts_store (#app:_)
  (st: store_t app)
  (ks: S.seq base_key)
  (ws: S.seq (app_value_nullable app.adm))
  : store_t app
  = if contains_only_app_keys_comp st ks && S.length ws = S.length ks then
      fun k -> if S.mem k ks then
               let i = S.index_mem k ks in
               let am = add_method_of st k in
               let gk = stored_key st k in
               let gv = AppV (S.index ws i) in
               let r = gk,gv in
               Some ({r; am})
             else
               st k
    else st

let puts (#app:_)
  (vs: vtls_t app{vs.valid})
  (ks: S.seq base_key)
  (ws: S.seq (app_value_nullable app.adm))
  : vs': vtls_t app{vs'.valid}
  = let st = puts_store vs.st ks ws in
    update_thread_store vs st

(* the specification of the high level verifier *)
let high_verifier_spec_base (app: app_params): Zeta.GenericVerifier.verifier_spec_base
  = let valid (vtls: vtls_t app): bool
      = vtls.valid
    in

    let clock (vtls: vtls_t app{valid vtls})
      = vtls.clock
    in

    let last_evict_key (vtls: vtls_t app{valid vtls})
      = vtls.last_evict_key
    in

    let tid (vtls: vtls_t app)
      = vtls.tid
    in

    let init (t: thread_id): vtls: vtls_t app {valid vtls /\ tid vtls = t}
      = init_thread_state app t
    in

    let slot_t = base_key in

    let get (k: slot_t) (vtls: vtls_t app {valid vtls}): option (record app)
      = if store_contains vtls.st k
        then Some (Some?.v (vtls.st k)).r
        else None
    in

    let open Zeta.GenericVerifier in
    { vtls_t = vtls_t app; valid; fail; clock; last_evict_key; tid; init; slot_t; app;
      get; puts; addm; addb; evictm; evictb; evictbm; nextepoch; verifyepoch }

module GV = Zeta.GenericVerifier

val lemma_high_verifier (aprm: app_params)
  : Lemma (ensures (GV.clock_monotonic_prop (high_verifier_spec_base aprm) /\
                    GV.thread_id_constant_prop (high_verifier_spec_base aprm) /\
                    GV.evict_prop (high_verifier_spec_base aprm) /\
                    GV.add_prop (high_verifier_spec_base aprm) /\
                    GV.addb_prop (high_verifier_spec_base aprm) /\
                    GV.evictb_prop (high_verifier_spec_base aprm)))
          [SMTPat (high_verifier_spec_base aprm)]

let high_verifier_spec (app: app_params) : Zeta.GenericVerifier.verifier_spec
  = high_verifier_spec_base app

let vlog_entry (aprm: app_params)
  = GV.verifier_log_entry (high_verifier_spec aprm)

let is_add_of_key (#app:_) (bk: base_key) (e: vlog_entry app)
  = let open Zeta.GenericVerifier in
    match e with
    | AddM _ k _ -> bk = k
    | AddB _ k _ _ -> bk = k
    | _ -> false

let add_method_of_entry (#app:_) (e: vlog_entry app{Zeta.GenericVerifier.is_add e})
  : add_method
  = let open Zeta.GenericVerifier in
    match e with
    | AddM _ _ _ -> MAdd
    | AddB _ _ _ _ -> BAdd

let refs_key #app (e: vlog_entry app) (k: base_key)
  = let open Zeta.GenericVerifier in
    let open FStar.Seq in
    match e with
    | AddM _ k' _ -> k' = k
    | AddB _ k' _ _ -> k' = k
    | EvictM k' _ -> k' = k
    | EvictB k' _ -> k' = k
    | EvictBM k' _ _ -> k' = k
    | NextEpoch -> false
    | VerifyEpoch -> false
    | RunApp _ _ ks -> mem k ks

(* an expanded variant of "referencing" that includes the ancestor keys as well *)
let exp_refs_key #app (e: vlog_entry app) (k: base_key)
  = let open Zeta.GenericVerifier in
    let open FStar.Seq in
    match e with
    | AddM _ k1 k2 -> k1 = k || k2 = k
    | AddB _ k' _ _ -> k' = k
    | EvictM k1 k2 -> k1 = k || k2 = k
    | EvictB k' _ -> k' = k
    | EvictBM k1 k2 _ -> k1 = k || k2 = k
    | NextEpoch -> false
    | VerifyEpoch -> false
    | RunApp _ _ ks -> mem k ks

val runapp_doesnot_change_nonref_slots
  (#app: _)
  (e: vlog_entry app {GV.RunApp? e})
  (vs: vtls_t app)
  (k: base_key)
  : Lemma (requires (let GV.RunApp _ _ ks = e in
                     let vs' = GV.verify_step e vs in
                     vs'.valid /\ not (S.mem k ks)))
          (ensures (let vs' = GV.verify_step e vs in
                    vs.st k == vs'.st k))

val runapp_doesnot_change_store_addmethod
  (#app:_)
  (ki: base_key)
  (e: vlog_entry app {Zeta.GenericVerifier.RunApp? e})
  (vs: vtls_t app)
  : Lemma (ensures (let vs_post = Zeta.GenericVerifier.verify_step e vs in
                    vs_post.valid ==>
                    store_contains vs.st ki ==>
                    store_contains vs_post.st ki /\
                    add_method_of vs.st ki = add_method_of vs_post.st ki))

val runapp_implies_store_contains
  (#app: _)
  (e: vlog_entry app {GV.is_appfn e})
  (vs: vtls_t _)
  (k: base_key)
  : Lemma (ensures (let GV.RunApp _ _ ks = e in
                    let vs_post = GV.verify_step e vs in
                    vs_post.valid ==>
                    S.mem k ks ==>
                    (let rs = GV.reads vs ks in
                     let i = S.index_mem k ks in
                     let ak,av = S.index rs i in
                     store_contains vs.st k /\
                     stored_key vs.st k = AppK ak /\
                     stored_value vs.st k = AppV av)))

val runapp_doesnot_change_slot_emptiness
  (#app: _)
  (e: vlog_entry app {GV.is_appfn e})
  (vs: vtls_t _)
  (k: base_key)
  : Lemma
          (ensures (let vs_post = GV.verify_step e vs in
                    vs_post.valid ==>
                    ((store_contains vs.st k) <==> (store_contains vs_post.st k))))

val runapp_doesnot_change_slot_key
  (#app:_)
  (ki: base_key)
  (e: vlog_entry app {Zeta.GenericVerifier.RunApp? e})
  (vs: vtls_t app)
  : Lemma (ensures (let vs_post = Zeta.GenericVerifier.verify_step e vs in
                    vs_post.valid ==>
                    store_contains vs.st ki ==>
                    store_contains vs_post.st ki /\
                    stored_key vs.st ki = stored_key vs_post.st ki))

val puts_valid
  (#app:_)
  (ki: base_key)
  (e: vlog_entry app {GV.is_appfn e})
  (vs: vtls_t app)
  (i:nat)
  : Lemma (ensures (let GV.RunApp f p ks = e in
                    let vs_post = GV.verify_step e vs in
                    vs_post.valid ==>
                    i < S.length ks ==>
                    (let rs = GV.reads vs ks in
                     let fn = appfn f in
                     let _,_,ws = fn p rs in
                     let k = S.index ks i in
                     store_contains vs_post.st k /\
                     stored_value vs_post.st k = AppV (S.index ws i))))
