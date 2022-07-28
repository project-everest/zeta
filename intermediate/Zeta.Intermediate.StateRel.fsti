module Zeta.Intermediate.StateRel

open Zeta.GenKey
open Zeta.Intermediate.VerifierConfig
open Zeta.Intermediate.Store
open Zeta.Intermediate.Verifier
open Zeta.Intermediate.Logs

module FE = FStar.FunctionalExtensionality
module HV = Zeta.High.Verifier
module GV = Zeta.GenericVerifier
module Merkle = Zeta.Merkle
module S = FStar.Seq

(* Relation between thread-local states
   * either both states have Failed
   * or both are Valid with equal contents
     (note that store_rel st st' enforces is_map st) *)
let vtls_rel #vcfg (vs:vtls_t vcfg) (vs':HV.vtls_t vcfg.app) : Type =
  vs.valid = vs'.valid /\
  (vs.valid ==> (vs.tid = vs'.tid /\
                 vs.clock = vs'.clock /\
                 vs.last_evict_key = vs'.last_evict_key /\
                 store_rel vs.st vs'.st))

let valid_logS_entry (#vcfg:_)
                     (vs: vtls_t vcfg{vs.valid})
                     (e: logS_entry _) =
  let st = vs.st in
  let s2k = Store.to_slot_state_map st in
  Logs.valid_logS_entry s2k e

let to_logk_entry (#vcfg:_)
                  (vs: vtls_t vcfg{vs.valid})
                  (e: logS_entry _{valid_logS_entry vs e}) =
  let st = vs.st in
  let s2k = Store.to_slot_state_map st in
  Logs.to_logk_entry s2k e

val lemma_empty_vtls_rel
  (#vcfg: verifier_config)
  (t:nat{t < vcfg.thread_count})
  : Lemma (ensures (let vss = init_thread_state vcfg t in
                    let vsk = HV.init_thread_state vcfg.app t in
                    vtls_rel vss vsk))

val lemma_runapp_simulates_spec
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (vs':_ {vtls_rel vs vs'})
      (e:logS_entry vcfg{GV.is_appfn e})
  : Lemma (requires (valid_logS_entry vs e))
          (ensures (let ek = to_logk_entry vs e in
                    vtls_rel (GV.verify_step e vs) (GV.verify_step ek vs')))

val lemma_app_res_rel
  (#vcfg:_)
  (vs: vtls_t vcfg{vs.valid})
  (vs': _ {vtls_rel vs vs'})
  (e: logS_entry vcfg {GV.is_appfn e})
  : Lemma (requires (valid_logS_entry vs e /\ (GV.verify_step e vs).valid))
          (ensures (let ek = to_logk_entry vs e in
                    vtls_rel (GV.verify_step e vs) (GV.verify_step ek vs') /\
                    GV.appfn_result e vs = GV.appfn_result ek vs'))

(* adding a key not in store to vaddm preserves the spec relationship *)
val lemma_vaddm_preserves_spec_new_key
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (vs':_ {vtls_rel vs vs'})
      (e:logS_entry _{GV.AddM? e})
  : Lemma (requires (let st = vs.st in
                     let GV.AddM (gk,gv) _  _ = e in
                     let k = to_base_key gk in
                     valid_logS_entry vs e /\
                     not (store_contains_key st k) /\
                     slot_points_to_is_merkle_points_to st))
          (ensures (let ek = to_logk_entry vs e in
                    vtls_rel (GV.verify_step e vs) (GV.verify_step ek vs')))

(* addb preserves spec relationship if the kew is not in store *)
val lemma_vaddb_preserves_spec_new_key
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (vs':_ {vtls_rel vs vs'})
      (e:logS_entry _{GV.AddB? e})
  : Lemma (requires (let st = vs.st in
                     let GV.AddB (gk,gv) _  _ _ = e in
                     let k = to_base_key gk in
                     valid_logS_entry vs e /\
                     not (store_contains_key st k)))
          (ensures (let ek = to_logk_entry vs e in
                    vtls_rel (GV.verify_step e vs) (GV.verify_step ek vs')))

val lemma_evictb_simulates_spec
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (vs':_ {vtls_rel vs vs'})
      (e:logS_entry vcfg{GV.EvictB? e})
  : Lemma (requires (let st = vs.st in
                     valid_logS_entry vs e /\
                     slot_points_to_is_merkle_points_to st /\
                     merkle_points_to_uniq st /\
                     merkle_points_to_desc st))
          (ensures (let ek = to_logk_entry vs e in
                    vtls_rel (GV.verify_step e vs) (GV.verify_step ek vs')))

val lemma_evictm_simulates_spec
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (vs':_ {vtls_rel vs vs'})
      (e:logS_entry vcfg{GV.EvictM? e})
  : Lemma (requires (let st = vs.st in
                     vtls_rel vs vs' /\
                     valid_logS_entry vs e /\
                     slot_points_to_is_merkle_points_to st /\
                     merkle_points_to_uniq st /\
                     merkle_points_to_desc st))
          (ensures (let ek = to_logk_entry vs e in
                    vtls_rel (GV.verify_step e vs) (GV.verify_step ek vs')))

val lemma_evictbm_simulates_spec
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (vs':_ {vtls_rel vs vs'})
      (e:logS_entry vcfg{GV.EvictBM? e})
  : Lemma (requires (let st = vs.st in
                     vtls_rel vs vs' /\
                     valid_logS_entry vs e /\
                     slot_points_to_is_merkle_points_to st /\
                     merkle_points_to_uniq st /\
                     merkle_points_to_desc st))
          (ensures (let ek = to_logk_entry vs e in
                    vtls_rel (GV.verify_step e vs) (GV.verify_step ek vs')))

val lemma_nextepoch_simulates_spec
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (vs':_ {vtls_rel vs vs'})
  : Lemma (requires (vtls_rel vs vs' /\
                     valid_logS_entry vs GV.NextEpoch))
          (ensures (let intspec = int_verifier_spec vcfg in
                    let hispec = HV.high_verifier_spec vcfg.app in
            vtls_rel #vcfg (GV.verify_step #intspec GV.NextEpoch vs) (GV.verify_step #hispec GV.NextEpoch vs')))

val lemma_verifyepoch_simulates_spec
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (vs':_ {vtls_rel vs vs'})
  : Lemma (requires (vtls_rel vs vs' /\
                     valid_logS_entry vs GV.VerifyEpoch))
          (ensures (let intspec = int_verifier_spec vcfg in
                    let hispec = HV.high_verifier_spec vcfg.app in
                    vtls_rel #vcfg (GV.verify_step #intspec GV.VerifyEpoch vs)
                                   (GV.verify_step #hispec GV.VerifyEpoch vs')))
