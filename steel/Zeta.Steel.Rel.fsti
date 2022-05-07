module Zeta.Steel.Rel

(* This module sets up the notation for relating steel concepts and spec level concepts. *)

open Zeta.App
open Zeta.Steel.KeyUtils

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module L = FStar.List.Tot
module GK = Zeta.GenKey
module K = Zeta.Key
module M = Zeta.Merkle
module GV = Zeta.GenericVerifier
module IL = Zeta.Intermediate.Logs
module IV = Zeta.Intermediate.Verifier
module AT = Zeta.Steel.ApplicationTypes
module T = Zeta.Steel.FormatsManual
module TSM = Zeta.Steel.ThreadStateModel

let app = AT.aprm
let value_type = AT.value_type

(* verifier_config for intermediate verifier *)
let i_vcfg = Zeta.Intermediate.VerifierConfig.VConfig
              (U16.v AT.store_size)
              app
              (U32.v AT.n_threads)

let s_key = T.key
let i_key = GK.key app

let s_base_key = T.base_key
let i_base_key = K.base_key

let s_desc_hash = T.descendent_hash
let i_desc_hash = M.desc_hash_t

let s_dir = bool
let i_dir = Zeta.BinTree.bin_tree_dir

(* merkle values *)
let s_mval = T.mval_value
let i_mval = M.value

let s_dval = option value_type
let i_dval = app_value_nullable app.adm

let s_val = T.value
let i_val = Zeta.Record.value app

let s_record = T.record
let i_record = Zeta.Record.record app

let s_slot_id = T.slot_id
let s_slot_id_r = T.slot  (* slot id with refinement that it is valid *)
let i_slot_id = Zeta.Intermediate.VerifierConfig.slot_id i_vcfg

let s_timestamp = T.timestamp
let i_timestamp = Zeta.Time.timestamp

let s_epoch = TSM.epoch_id
let i_epoch = Zeta.Time.epoch

let s_tid = T.thread_id
let i_tid = Zeta.Thread.thread_id

let s_fid = U8.t
let i_fid = appfn_id app

let s_log_entry = T.log_entry
let i_log_entry = IV.logS_entry i_vcfg

let s_log = TSM.log
let i_log = IL.logS i_vcfg

let s_hashfn = Zeta.Steel.HashValue.hashfn
let i_hashfn = Zeta.HashFunction.hashfn #app

let s_hash_value = T.hash_value
let i_hash_value = Zeta.Hash.hash_value

let s_add_method = TSM.add_method
let i_add_method = Zeta.High.Verifier.add_method

let s_store_entry = TSM.store_entry
let i_store_entry = Zeta.Intermediate.Store.vstore_entry i_vcfg

let s_store = TSM.contents
let i_store = Zeta.Intermediate.Store.vstore i_vcfg

let s_thread_state = TSM.thread_state_model
let i_thread_state = Zeta.Intermediate.Verifier.vtls_t i_vcfg

val lift_key (k: s_key)
  : GTot i_key

val lower_key (k: i_key)
  : GTot (k': s_key { lift_key k' = k })

val lemma_lower_lift_key (k: s_key)
  : Lemma (ensures (lower_key (lift_key k) == k))

let related_key (sk: s_key) (ik: i_key)
  = lower_key ik == sk

let related_base_key (sk: s_base_key) (ik: i_base_key)
  = lower_base_key ik == sk

val related_root (sk: s_key) (ik: i_key)
  : Lemma (requires (related_key sk ik))
          (ensures (TSM.is_root_key sk <==> ik = GK.IntK Zeta.BinTree.Root))

val related_root_inv (_:unit)
  : Lemma (ensures (let rk = T.root_key in
                    let i_rk = GK.IntK Zeta.BinTree.Root in
                    related_key rk i_rk))

let related_desc_dir (sd: s_dir) (id: i_dir)
  = sd = Zeta.BinTree.Left? id

val lemma_related_key_proper_descendent (sk0 sk1: s_base_key) (ik0 ik1: i_base_key)
  : Lemma (requires (related_base_key sk0 ik0 /\ related_base_key sk1 ik1))
          (ensures (is_proper_descendent sk0 sk1 <==> Zeta.BinTree.is_proper_desc ik0 ik1) /\
                   (is_proper_descendent sk0 sk1 ==>
                    (related_desc_dir (desc_dir sk0 sk1) (Zeta.BinTree.desc_dir ik0 ik1))))

val lemma_related_base_key (sk: s_key) (ik: i_key)
  : Lemma (requires (related_key sk ik))
          (ensures (let s = TSM.to_base_key sk in
                    let i = GK.to_base_key ik in
                    related_base_key s i))

val related_app_key (sk: s_key) (ik: i_key)
  : Lemma (requires (related_key sk ik /\
                     T.ApplicationKey? sk))
          (ensures (GK.AppK? ik /\
                    (let T.ApplicationKey ak = sk in
                     let GK.AppK i_ak = ik in
                     ak = i_ak)))

let lift_hash_value (shv: s_hash_value)
  : i_hash_value
  = Zeta.Steel.BitUtils.bitvec_of_u256 shv

let related_hash_value (shv: s_hash_value) (ihv: i_hash_value)
  = ihv == lift_hash_value shv

val related_zero (_:unit)
  : Lemma (ensures (related_hash_value TSM.zero Zeta.Hash.zero))

let related_desc_hash (s_hash: s_desc_hash)
                      (i_hash: i_desc_hash)
  = let open T in
    let open M in
    let open Zeta.Steel.BitUtils in
    match s_hash, i_hash with
    | Dh_vnone (), Empty -> True
    | Dh_vsome dhd, Desc k h b ->
      related_base_key dhd.dhd_key k /\
      related_hash_value dhd.dhd_h h /\
      Vtrue? dhd.evicted_to_blum == b
    | _ -> False
  
val lift_desc_hash (sdh: s_desc_hash)
  : GTot (idh: i_desc_hash { related_desc_hash sdh idh })

let related_mval (smv: s_mval) (imv: i_mval)
  = let open T in
    let open M in
    related_desc_hash smv.l imv.left /\
    related_desc_hash smv.r imv.right
  
val lift_mval (smv: s_mval)
  : GTot (imv: i_mval { related_mval smv imv })

let related_dval (sdv: s_dval) (idv: i_dval)
  = match sdv, idv with
    | None, Null -> True
    | Some sv, DValue iv -> sv == iv
    | _ -> False

val lift_dval (sdv: s_dval)
  : GTot (idv: i_dval {related_dval sdv idv})

let related_val (sv: s_val) (iv: i_val)
  = let open Zeta.Record in
    let open T in
    match sv, iv with
    | MValue smv, IntV imv -> related_mval smv imv
    | DValue sdv, AppV idv -> related_dval sdv idv
    | _ -> False
  
val lift_val (sv: s_val)
  : GTot (iv: i_val { related_val sv iv })

let related_record (sr: s_record) (ir: i_record)
  = let open T in
    let open Zeta.Record in
    let sk, sv = sr in
    let ik, iv = ir in
    related_key sk ik /\
    related_val sv iv

val lift_record (sr: s_record)
  : GTot (ir: i_record { related_record sr ir })

let valid_slot (s: s_slot_id)
  = TSM.check_slot_bounds s

let lift_slot (ss: s_slot_id {valid_slot ss})
  : i_slot_id
  = U16.v ss

let lift_slot_r (ss: s_slot_id_r)
  : i_slot_id
  = U16.v ss

let related_slot (ss: s_slot_id) (is: i_slot_id)
  = valid_slot ss /\ lift_slot ss = is

let related_slot_r (ss: s_slot_id_r) (is: i_slot_id)
  = lift_slot ss = is

val lift_timestamp (st: s_timestamp)
  : i_timestamp

let related_timestamp (st: s_timestamp) (it: i_timestamp)
  = it == lift_timestamp st

val related_next (st: s_timestamp) (it: i_timestamp)
  : Lemma (requires (related_timestamp st it))
          (ensures (match TSM.next st with
                    | None -> True
                    | Some st' -> related_timestamp st' (Zeta.Time.next it)))

val related_max (st1 st2: s_timestamp) (it1 it2: i_timestamp)
  : Lemma (requires (related_timestamp st1 it1 /\ related_timestamp st2 it2))
          (ensures (related_timestamp (TSM.max st1 st2) (Zeta.Time.max it1 it2)))

val related_timestamp_lt (st1 st2: s_timestamp) (it1 it2: i_timestamp)
  : Lemma (requires (related_timestamp st1 it1 /\ related_timestamp st2 it2))
          (ensures (st1 `TSM.timestamp_lt` st2 <==> it1 `Zeta.Time.ts_lt` it2))

val related_timestamp_zero (_: unit)
  : Lemma (ensures (let st = TSM.zero_clock in
                    let it = { Zeta.Time.e = 0 ; Zeta.Time.c = 0 } in
                    related_timestamp st it))

let lift_epoch (s: s_epoch)
  : i_epoch
  = U32.v s

let related_epoch (s: s_epoch) (i: i_epoch)
  = i == lift_epoch s

val related_timestamp_epoch (st: s_timestamp) (it: i_timestamp)
  : Lemma (requires (related_timestamp st it))
          (ensures (let se = TSM.epoch_of_timestamp st in
                    let ie = it.Zeta.Time.e in
                    related_epoch se ie))

val related_epoch_incr (s: s_epoch) (i: i_epoch)
  : Lemma (requires (related_epoch s i /\ FStar.UInt.fits (U32.v s + 1) 32))
          (ensures (related_epoch (U32.add s U32.one) (i+1)))

val related_epoch_shift (se: s_epoch) (ie: i_epoch)
  : Lemma (requires related_epoch se ie)
          (ensures (let open Zeta.Time in
                    let st : T.timestamp = { epoch  = se; counter = 0ul } in
                    let it = {e = ie; c = 0} in
                    related_timestamp st it))

  
let lift_tid (st: s_tid)
  : i_tid
  = U16.v st

let related_tid (st: s_tid) (it: i_tid)
  = lift_tid st == it

val related_init_value (sk: s_key) (ik: i_key)
  : Lemma (requires (related_key sk ik))
          (ensures (related_val (TSM.init_value sk) (Zeta.Record.init_value ik)))

let related_add_method (sam: s_add_method) (iam: i_add_method)
  = let open Zeta.High.Verifier in
    match sam, iam with
    | TSM.MAdd, MAdd -> True
    | TSM.BAdd, BAdd -> True
    | _ -> False

