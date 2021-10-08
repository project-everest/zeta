module Zeta.Intermediate.Verify

open Zeta.BinTree
open Zeta.Hash
open Zeta.HashFunction
open Zeta.Thread
open Zeta.Time
open Zeta.App
open Zeta.Key
open Zeta.GenKey
open Zeta.Merkle
open Zeta.Record
open Zeta.SeqAux
open Zeta.Intermediate.SlotKeyRel
open Zeta.Intermediate.VerifierConfig
open Zeta.Intermediate.Store

module FE = FStar.FunctionalExtensionality
module HV = Zeta.High.Verifier
module GV = Zeta.GenericVerifier
module Merkle = Zeta.Merkle
module S = FStar.Seq

(* Thread-local state
   id     : thread id
   st     : thread local store
   clock  : current timestamp
   hadd   : add set hash
   hevict : evict set hash *)
noeq
type vtls_t (vcfg: verifier_config) = {
  (* is the verifier valid *)
  valid: bool;

  (* thread id *)
  tid: thread_id;

  (* clock *)
  clock: timestamp;

  (* verifier store *)
  st: vstore vcfg;
}

let thread_store_size #vcfg (vs: vtls_t vcfg): nat =
  Seq.length vs.st

let update_thread_store #vcfg (vs:vtls_t vcfg {vs.valid}) (st:vstore vcfg) : vtls_t _
  = { valid = vs.valid; tid = vs.tid; clock = vs.clock; st }

let update_thread_clock #vcfg (vs:vtls_t vcfg {vs.valid}) (clock:timestamp): vtls_t _
  = { valid = vs.valid; tid = vs.tid; clock ; st = vs.st }

let fail (#vcfg:_) (vtls: vtls_t vcfg):
  vtls': vtls_t vcfg {not (vtls'.valid)}
  = { valid = false; tid = vtls.tid; clock = vtls.clock; st = vtls.st }

(* addm params *)
noeq type addm_param (vcfg: verifier_config) =
  | AMP: s: slot_id vcfg ->
         r: record vcfg.app ->
         s': slot_id vcfg ->
         vs': vtls_t vcfg{vs'.valid} -> addm_param vcfg

let addm_key #vcfg (a: addm_param vcfg)
  = match a with
    | AMP _ (gk,_) _ _ -> gk

let addm_base_key #vcfg (a: addm_param vcfg) =
  match a with
  | AMP _ (gk,_) _ _ -> to_base_key gk

let addm_slot #vcfg (a: addm_param vcfg) =
  match a with
  | AMP s _ _ _ -> s

let addm_anc_slot #vcfg (a: addm_param vcfg) =
  match a with
  | AMP _ _ s' _ -> s'

let addm_store_pre #vcfg (a: addm_param vcfg) =
  match a with
  | AMP _ _ _ vs' ->  vs'.st

let addm_precond1 #vcfg (a: addm_param vcfg) =
  let st' = addm_store_pre a in
  match a with
  | AMP s (gk,gv) s' _ ->
  s <> s' /\
  inuse_slot st' s' /\
  empty_slot st' s /\
  (let k' = stored_base_key st' s' in
   is_proper_desc (to_base_key gk) k')

let addm_value_pre #vcfg (a: addm_param vcfg {addm_precond1 a})  =
  match a with
  | AMP _ (k,v) _ _ -> v

let addm_hash_val_pre #vcfg (a: addm_param vcfg {addm_precond1 a}) =
  hashfn (addm_value_pre a)

let addm_anc_key #vcfg (a: addm_param vcfg {addm_precond1 a}): merkle_key =
  stored_base_key (addm_store_pre a) (addm_anc_slot a)

let addm_anc_val_pre #vcfg (a: addm_param vcfg {addm_precond1 a}) =
  let st' = addm_store_pre a in
  let s' = addm_anc_slot a in
  to_merkle_value (stored_value st' s')

let addm_dir #vcfg (a: addm_param vcfg {addm_precond1 a}):bin_tree_dir =
  desc_dir (addm_base_key a) (addm_anc_key a)

let addm_precond2 #vcfg (a: addm_param vcfg) =
  addm_precond1 a /\
  (let mv' = addm_anc_val_pre a in
   let d = addm_dir a in
   Merkle.points_to_none mv' d \/                          // case A: ancestor points to nothing along d
   Merkle.points_to mv' d (addm_base_key a) \/                  // case B: ancestor points to key being added
   is_proper_desc (Merkle.pointed_key mv' d) (addm_base_key a)) // case C: ancestor points to some key below key being added

// case A:
let addm_anc_points_null #vcfg (a: addm_param vcfg{addm_precond2 a}) =
  Merkle.points_to_none (addm_anc_val_pre a) (addm_dir a)

// case B:
let addm_anc_points_to_key #vcfg (a: addm_param vcfg{addm_precond2 a}) =
  Merkle.points_to (addm_anc_val_pre a) (addm_dir a) (addm_base_key a)

// desc hash at ancestor along addm direction
let addm_desc_hash_dir #vcfg (a: addm_param vcfg{addm_precond2 a /\ addm_anc_points_to_key a}) =
  Merkle.desc_hash (addm_anc_val_pre a) (addm_dir a)

// case C:
let addm_anc_points_to_desc #vcfg (a: addm_param vcfg{addm_precond2 a}) =
  let mv' = addm_anc_val_pre a in
  let d = addm_dir a in
  Merkle.points_to_some mv' d /\
  is_proper_desc (Merkle.pointed_key mv' d) (addm_base_key a)

// desc key for case C:
let addm_desc #vcfg (a:addm_param vcfg{addm_precond2 a /\ addm_anc_points_to_desc a}):
  (k2:base_key {is_proper_desc k2 (addm_base_key a)}) =
  Merkle.pointed_key (addm_anc_val_pre a) (addm_dir a)

let addm_desc_dir #vcfg (a: addm_param vcfg{addm_precond2 a /\ addm_anc_points_to_desc a})
  : bin_tree_dir
  = desc_dir (addm_desc a) (addm_base_key a)

let addm_precond #vcfg (a: addm_param vcfg) =
  let st = addm_store_pre a in
  let s' = addm_anc_slot a in
  addm_precond2 a /\
  (let d = addm_dir a in
   (addm_anc_points_null a ==> (addm_value_pre a = init_value (addm_key a) /\
                              points_to_none st s' d)) /\
   (addm_anc_points_to_key a ==> (addm_desc_hash_dir a = Merkle.Desc (addm_base_key a) (addm_hash_val_pre a) false) /\
                                points_to_none st s' d) /\
   (addm_anc_points_to_desc a ==> (addm_value_pre a = init_value (addm_key a))))

(* does the ancestor point to the descendant slot *)
let addm_has_desc_slot #vcfg (a: addm_param vcfg{addm_precond a}) =
  addm_anc_points_to_desc a /\
  (let s' = addm_anc_slot a in
   let st' = addm_store_pre a in
   let d = addm_dir a in
   points_to_some_slot st' s' d)

let addm_desc_slot #vcfg (a: addm_param vcfg{addm_precond a /\ addm_has_desc_slot a}) =
  let s' = addm_anc_slot a in
  let st' = addm_store_pre a in
  let d = addm_dir a in
  pointed_slot st' s' d

let addm_value_postcond #vcfg (a: addm_param vcfg{addm_precond a})
  (v: value vcfg.app{compatible (addm_key a) v}) =
  (addm_anc_points_null a /\ (v = addm_value_pre a)) \/
  (addm_anc_points_to_key a /\ (v = addm_value_pre a)) \/
  (addm_anc_points_to_desc a /\
    (let dd = addm_desc_dir a in
     let odd = other_dir dd in
     let mv = to_merkle_value v in
     desc_hash mv dd = desc_hash (addm_anc_val_pre a) (addm_dir a) /\
     desc_hash mv odd = Empty))

let addm_slot_points_postcond #vcfg (a: addm_param vcfg{addm_precond a}) (st: vstore vcfg) =
  let s = addm_slot a in
  let st' = addm_store_pre a in
  let s' = addm_anc_slot a in
  let d = addm_dir a in
  inuse_slot st s /\
  ((addm_anc_points_null a /\ points_to_none st s Left /\ points_to_none st s Right) \/
   (addm_anc_points_to_key a /\ points_to_none st s Left /\ points_to_none st s Right) \/
   (addm_anc_points_to_desc a /\ (points_to_info st s (addm_desc_dir a) = points_to_info st' s' d) /\
                                 points_to_none st s (other_dir (addm_desc_dir a))))

(* post-condition on addm slot *)
let addm_slot_postcond #vcfg (a: addm_param vcfg{addm_precond a}) (st: vstore vcfg) =
  let s = addm_slot a in
  inuse_slot st s  /\                          // in use
  stored_key st s = addm_key a   /\            // stores key k
  add_method_of st s = HV.MAdd /\            // stores the correct add method
  addm_value_postcond a (stored_value st s) /\ // value postcond
  addm_slot_points_postcond a st

let addm_anc_val_postcond #vcfg (a: addm_param vcfg{addm_precond a}) (mv: Merkle.value) =
  let mv' = addm_anc_val_pre a in
  let d = addm_dir a in
  let od = other_dir d in
  desc_hash mv od = desc_hash mv' od /\               // merkle value unchanged in other direction
  Merkle.points_to mv d (addm_base_key a) /\                           // merkle value points to k in addm direction
  Merkle.evicted_to_blum mv d = false

let addm_anc_slot_points_postcond #vcfg (a: addm_param vcfg{addm_precond a}) (st: vstore vcfg) =
  let st' = addm_store_pre a in
  let s' = addm_anc_slot a in
  let d = addm_dir a in
  let od = other_dir d in
  inuse_slot st s' /\
  points_to_info st s' od = points_to_info st' s' od /\        // points to does not change in other dir
  points_to_dir st s' d (addm_slot a)

let addm_anc_slot_postcond #vcfg (a: addm_param vcfg{addm_precond a}) (st: vstore vcfg) =
  let s' = addm_anc_slot a in
  let st' = addm_store_pre a in
  inuse_slot st s' /\
  stored_base_key st s' = addm_anc_key a /\
  add_method_of st s' = add_method_of st' s' /\
  addm_anc_val_postcond a (to_merkle_value (stored_value st s')) /\
  addm_anc_slot_points_postcond a st

let addm_desc_slot_postcond #vcfg (a: addm_param vcfg{addm_precond a /\ addm_has_desc_slot a}) (st: vstore vcfg) =
  let sd = addm_desc_slot a in
  let st' = addm_store_pre a in
  inuse_slot st sd /\ inuse_slot st' sd /\
  stored_key st sd = stored_key st' sd /\
  stored_value st sd = stored_value st' sd /\
  add_method_of st sd = add_method_of st' sd

let addm_postcond #vcfg (a: addm_param vcfg{addm_precond a}) (vs: vtls_t vcfg) =
  let vs' = a.vs' in

  (* if the precond holds then addm succeeds *)
  vs.valid /\
  (vs.tid = vs'.tid /\ vs.clock = vs'.clock /\                // everything except store is unchanged
   (addm_has_desc_slot a /\
    identical_except3 vs.st vs'.st (addm_slot a) (addm_anc_slot a) (addm_desc_slot a) /\
    addm_desc_slot_postcond a vs.st
    \/
    ~ (addm_has_desc_slot a) /\
    identical_except2 vs.st vs'.st (addm_slot a) (addm_anc_slot a)) /\
   addm_slot_postcond a vs.st /\                                      // postcond on slot s
   addm_anc_slot_postcond a vs.st)                                    // postcond on slot s'

val addm (#vcfg:verifier_config)
  (r:record vcfg.app)
  (s:slot_id vcfg)
  (s':slot_id vcfg)
  (vs: vtls_t vcfg {vs.valid}):
  (vs': vtls_t vcfg {let a = AMP s r s' vs in
                     addm_precond a /\ addm_postcond a vs' \/
                     ~(addm_precond a) /\ ~vs'.valid})

let evictm #vcfg (s:slot_id vcfg) (s':slot_id vcfg) (vs: vtls_t vcfg {vs.valid}): vtls_t vcfg =
  let st = vs.st in
  (* check store contains s and s' *)
  if empty_slot st s || empty_slot st s' then fail vs
  else if s = s' then fail vs
  else
    let k = stored_base_key st s in
    let v = stored_value st s in
    let k' = stored_base_key st s' in
    let v' = stored_value st s' in
    (* check k is a proper descendent of k' *)
    if not (is_proper_desc k k') then fail vs
    (* check k does not have a (merkle) child in the store *)
    else if points_to_some_slot st s Left || points_to_some_slot st s Right then fail vs
    else
      let d = desc_dir k k' in
      let v' = to_merkle_value v' in
      let dh' = desc_hash v' d in
      let h = hashfn v in
      match dh' with
      | Empty -> fail vs
      | Desc k2 h2 b2 ->
          if k2 <> k then fail vs
          (* TODO: explain the following "spurious checks" *)
          (* if s has a parent that is different from s' then Fail *)
          else if has_parent st s && (parent_slot st s <> s' || parent_dir st s <> d) then fail vs
          (* if s has no parent, but s' points to something then Fail *)
          else if not (has_parent st s) && (points_to_some_slot st s' d) then fail vs
          (* s and s' cannot be the same *)
          else if s = s' then fail vs
          else
            let v'_upd = Merkle.update_value v' d k h false in
            let st_upd = update_value st s' (IntV v'_upd) in
            let st_upd = mevict_from_store st_upd s s' d in
            update_thread_store vs st_upd

let addb #vcfg (r:record vcfg.app) (s:slot_id vcfg) (t:timestamp) (j:thread_id) (vs:vtls_t _ {vs.valid})
  : vtls_t _ =
  (* epoch of timestamp of last evict *)
  let st = vs.st in
  let (k,v) = r in
  if k = IntK Root then fail vs
  (* check store contains slot s *)
  else if inuse_slot st s then fail vs
  else
    let clk = max vs.clock (next t) in
    let vs = update_thread_clock vs clk in
    (* add record to store *)
    let st = badd_to_store st s r in
    update_thread_store vs st

let sat_evictb_checks #vcfg (s:slot_id vcfg) (t:timestamp) (vs:vtls_t _ {vs.valid}): bool =
  let st = vs.st in
  inuse_slot st s &&
  (
    let k = stored_key st s in

    (* check key at s is not root *)
    k <> IntK Root &&

    (* check time of evict < current time *)
    vs.clock `ts_lt` t &&

    (* check k has no (merkle) children n the store *)
    points_to_none st s Left && points_to_none st s Right
  )

let vevictb_update_hash_clock #vcfg (s:slot_id vcfg) (t:timestamp)
  (vs:vtls_t _ {vs.valid /\ sat_evictb_checks s t vs}):
  (vs':vtls_t _ {vs'.valid}) =
  (* update clock and return *)
  update_thread_clock vs t

let evictb #vcfg (s:slot_id vcfg) (t:timestamp) (vs:vtls_t _ {vs.valid}): vtls_t _ =
  let st = vs.st in
  if not (sat_evictb_checks s t vs) || add_method_of st s <> HV.BAdd then fail vs
  else
    let k = stored_key st s in
    let v = stored_value st s in
    let vs = vevictb_update_hash_clock s t vs in
    let st_upd = bevict_from_store st s in
    update_thread_store vs st_upd

let evictbm #vcfg (s:slot_id vcfg) (s':slot_id vcfg) (t:timestamp)
  (vs:vtls_t vcfg {vs.valid}): vtls_t vcfg =
  let st = vs.st in
  if s = s' then fail vs
  else if not (sat_evictb_checks s t vs) || add_method_of st s <> HV.MAdd then fail vs
  else if empty_slot st s' then fail vs
  else
    let k = stored_base_key st s in
    let k' = stored_base_key st s' in
    let v' = stored_value st s' in
    (* check k is a proper desc of k' *)
    if not (is_proper_desc k k') then fail vs
    else
      let v' = to_merkle_value v' in
      let d = desc_dir k k' in
      let dh' = desc_hash v' d in
      match dh' with
      | Empty -> fail vs
      | Desc k2 h2 b2 ->
          if k2 <> k || b2 then fail vs
          else if not (has_parent st s) || parent_slot st s <> s' || parent_dir st s <> d then fail vs
          else
            (* update the evict hash and the clock *)
            let vs = vevictb_update_hash_clock s t vs in
            // assert(thread_store vs == thread_store vs_upd);

            (* update the hash at k' *)
            let v'_upd = Merkle.update_value v' d k h2 true in
            let st = update_value st s' (IntV v'_upd) in

            (* evict s' from store *)
            let st = mevict_from_store st s s' d in
            update_thread_store vs st

let nextepoch #vcfg (vs: vtls_t vcfg{vs.valid}): vtls_t _ =
  let e = vs.clock.e + 1 in
  let clk = {e; c = 0} in
  update_thread_clock vs clk

let verifyepoch #vcfg (vs: vtls_t vcfg{vs.valid})
  = vs

let init_store (vcfg:_) (t: thread_id): vstore _
  = let st = empty_store vcfg in
    if t = 0 then madd_to_store_root st 0 (init_value (IntK Root))
    else st

let init_thread_state vcfg (tid: thread_id): vtls_t vcfg =
  let st = init_store vcfg tid in
  { valid = true; tid; clock = {e = 0; c = 0}; st  }

val puts (#vcfg:_)
  (vs: vtls_t vcfg{vs.valid})
  (ks: S.seq (slot_id vcfg))
  (ws: S.seq (app_value_nullable vcfg.app.adm))
  : vs': vtls_t vcfg{vs'.valid}

let int_verifier_spec_base (vcfg: verifier_config) : GV.verifier_spec_base
  = let valid (vtls: vtls_t vcfg): bool
      = vtls.valid
    in

    let clock (vtls: vtls_t vcfg{valid vtls})
      = vtls.clock
    in

    let tid (vtls: vtls_t vcfg)
      = vtls.tid
    in

    let init (t: thread_id): vtls: vtls_t vcfg {valid vtls /\ tid vtls = t}
      = init_thread_state vcfg t
    in

    let slot_t = slot_id vcfg in

    let get (s: slot_t) (vtls: vtls_t vcfg {valid vtls}): option (record vcfg.app)
      = if inuse_slot vtls.st s
        then Some (stored_record vtls.st s)
        else None
    in

    let open Zeta.GenericVerifier in
    { vtls_t = vtls_t vcfg; valid; fail; clock; tid; init; slot_t; app = vcfg.app;
      get; puts; addm; addb; evictm; evictb; evictbm; nextepoch; verifyepoch }

val lemma_int_verifier (vcfg: verifier_config)
  : Lemma (ensures (GV.clock_monotonic_prop (int_verifier_spec_base vcfg) /\
                    GV.thread_id_constant_prop (int_verifier_spec_base vcfg) /\
                    GV.evict_prop (int_verifier_spec_base vcfg) /\
                    GV.add_prop (int_verifier_spec_base vcfg) /\
                    GV.addb_prop (int_verifier_spec_base vcfg) /\
                    GV.evictb_prop (int_verifier_spec_base vcfg)))
          [SMTPat (int_verifier_spec_base vcfg)]

let int_verifier_spec (vcfg: verifier_config): GV.verifier_spec
  = int_verifier_spec_base vcfg

let logS_entry (vcfg:_)
  = GV.verifier_log_entry (int_verifier_spec vcfg)

val lemma_addm_props (#vcfg:_)
                     (vs':vtls_t vcfg{vs'.valid})
                     (e:logS_entry _{GV.AddM? e}):
  Lemma (requires ((GV.verify_step e vs').valid))
        (ensures (let GV.AddM (gk,gv) s s' = e in
                  let st' = vs'.st in
                  let k = to_base_key gk in
                  inuse_slot st' s' /\
                  (let k' = stored_base_key st' s' in
                   is_proper_desc k k' /\
                   is_merkle_key k' /\
                   (let mv' = to_merkle_value (stored_value st' s') in
                    let d = desc_dir k k' in
                    (Merkle.points_to_none mv' d ||
                     is_desc (Merkle.pointed_key mv' d) k)))))

(*

(* verifiability implies consistency of the log *)
val lemma_verifiable_implies_consistent_log (#vcfg:_) (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l}):
  Lemma (ensures (let st = thread_store vsinit in
                  let s2k = to_slot_state_map st in
                  consistent_log s2k l))
        [SMTPat (verifiable vsinit l)]

(* the association of slot -> keys in store is what is mandated by the log *)
(* TODO: do we really need this *)
val lemma_s2k_store_eq_s2k_log (#vcfg:_) (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l}):
  Lemma (ensures (let stinit = thread_store vsinit in
                  let s2kinit = S.to_slot_state_map stinit in
                  let stend = thread_store (verify vsinit l) in
                  let s2kend = S.to_slot_state_map stend in
                  let s2klog = L.to_slot_state_map s2kinit l in
                  FE.feq s2kend s2klog))
        [SMTPat (verifiable vsinit l)]

let valid_logS_entry (#vcfg:_)
                     (vs: vtls vcfg{Valid? vs})
                     (e: logS_entry _) =
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  L.valid_logS_entry s2k e

let to_logK_entry (#vcfg:_)
                  (vs: vtls vcfg{Valid? vs})
                  (e: logS_entry _{valid_logS_entry vs e}) =
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  L.to_logK_entry s2k e

(* if there are no verification failures, slot_points to implies merkle points to property is
 * propagates *)
val lemma_verifiable_implies_slot_is_merkle_points_to (#vcfg:_)
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e))))

let all_epoch_hashes_equal (h1 h2: epoch_hash) =
  forall (ep: epoch). h1 ep = h2 ep

(* Relation between thread-local states
   * either both states have Failed
   * or both are Valid with equal contents
     (note that store_rel st st' enforces is_map st) *)
let vtls_rel #vcfg (vs:vtls vcfg) (vs':Spec.vtls) : Type =
  (Failed? vs /\ Spec.Failed? vs') \/
  (Valid? vs /\ Spec.Valid? vs' /\
   (let Valid id st clk ha he = vs in
    let Spec.Valid id' st' clk' _ ha' he' = vs' in
    store_rel st st' /\ id = id' /\ clk = clk' /\ all_epoch_hashes_equal ha ha' /\ all_epoch_hashes_equal he he'))

val lemma_vget_simulates_spec
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)
      (e:logS_entry vcfg{Get_S? e})
  : Lemma (requires (vtls_rel vs vs' /\
                     valid_logS_entry vs e))
          (ensures (let ek = to_logK_entry vs e in
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))

val lemma_vget_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{Get_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))

val lemma_vput_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{Put_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))
          [SMTPat (verify_step vs e)]

val lemma_vput_simulates_spec
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)
      (e:logS_entry vcfg{Put_S? e})
  : Lemma (requires (vtls_rel vs vs' /\
                     valid_logS_entry vs e))
          (ensures (let ek = to_logK_entry vs e in
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))

(* if the key is not present in store and store is a map, then store remains a map after add *)
val lemma_vaddm_preserves_ismap_new_key
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{AddM_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let AddM_S _ (k,_) _ = e in
                     is_map st /\ not (store_contains_key st k)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))

(* adding a key not in store to vaddm preserves the spec relationship *)
val lemma_vaddm_preserves_spec_new_key
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)
      (e:logS_entry _{AddM_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let AddM_S _ (k,_) _ = e in
                     vtls_rel vs vs' /\
                     valid_logS_entry vs e /\
                     not (store_contains_key st k) /\
                     slot_points_to_is_merkle_points_to st))
          (ensures (let ek = to_logK_entry vs e in
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))

(* if the key is not present in store and store is a map, then store remains a map after add *)
val lemma_vaddb_preserves_ismap_new_key
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{AddB_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let AddB_S _ (k,_) _ _ = e in
                     is_map st /\ not (store_contains_key st k)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))

(* addb preserves spec relationship if the kew is not in store *)
val lemma_vaddb_preserves_spec_new_key
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)
      (e:logS_entry _{AddB_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let AddB_S _ (k,_) _ _ = e in
                     vtls_rel vs vs' /\
                     valid_logS_entry vs e /\
                     not (store_contains_key st k)))
          (ensures (let ek = to_logK_entry vs e in
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))

val lemma_evictb_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{EvictB_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))

val lemma_evictb_simulates_spec
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)
      (e:logS_entry vcfg{EvictB_S? e})
  : Lemma (requires (let st = thread_store vs in
                     vtls_rel vs vs' /\
                     valid_logS_entry vs e /\
                     slot_points_to_is_merkle_points_to st /\
                     merkle_points_to_uniq st /\
                     merkle_points_to_desc st))
          (ensures (let ek = to_logK_entry vs e in
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))

val lemma_evictm_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{EvictM_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))

val lemma_evictm_simulates_spec
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)
      (e:logS_entry vcfg{EvictM_S? e})
  : Lemma (requires (let st = thread_store vs in
                     vtls_rel vs vs' /\
                     valid_logS_entry vs e /\
                     slot_points_to_is_merkle_points_to st /\
                     merkle_points_to_uniq st /\
                     merkle_points_to_desc st))
          (ensures (let ek = to_logK_entry vs e in
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))

val lemma_evictbm_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{EvictBM_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))

val lemma_evictbm_simulates_spec
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)
      (e:logS_entry vcfg{EvictBM_S? e})
  : Lemma (requires (let st = thread_store vs in
                     vtls_rel vs vs' /\
                     valid_logS_entry vs e /\
                     slot_points_to_is_merkle_points_to st /\
                     merkle_points_to_uniq st /\
                     merkle_points_to_desc st))
          (ensures (let ek = to_logK_entry vs e in
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))

val lemma_nextepoch_simulates_spec
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)
  : Lemma (requires (vtls_rel vs vs' /\
                     valid_logS_entry vs NextEpoch))
          (ensures (let ek = to_logK_entry vs NextEpoch in
                    vtls_rel (verify_step vs NextEpoch) (Spec.t_verify_step vs' ek)))

val lemma_nextepoch_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs NextEpoch) ==> S.is_map (thread_store (verify_step vs NextEpoch))))

val lemma_verifyepoch_simulates_spec
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)
  : Lemma (requires (vtls_rel vs vs' /\
                     valid_logS_entry vs VerifyEpoch))
          (ensures (let ek = to_logK_entry vs VerifyEpoch in
                    vtls_rel (verify_step vs VerifyEpoch) (Spec.t_verify_step vs' ek)))

val lemma_verifyepoch_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs VerifyEpoch) ==> S.is_map (thread_store (verify_step vs VerifyEpoch))))


let blum_evict_elem #vcfg (vs:vtls vcfg{Valid? vs})
                    (e:logS_entry _ {is_evict_to_blum e /\ Valid? (verify_step vs e)})
                    (tid: thread_id): ms_hashfn_dom =
  let st = thread_store vs in
  match e with
  | EvictB_S s t ->
    let k = stored_key st s in
    let v = stored_value st s in
    MHDom (k,v) t tid
  | EvictBM_S s _ t ->
    let k = stored_key st s in
    let v = stored_value st s in
    MHDom (k,v) t tid
*)
