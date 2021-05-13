module Veritas.Intermediate.Verify

open Veritas.BinTree
open Veritas.Hash
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.MultiSetHashDomain
open Veritas.Record
open Veritas.SeqAux
open Veritas.Intermediate.SlotKeyRel
open Veritas.Intermediate.Logs
open Veritas.Intermediate.VerifierConfig
open Veritas.Intermediate.Store

module FE = FStar.FunctionalExtensionality
module Spec = Veritas.Verifier
module L = Veritas.Intermediate.Logs
module S = Veritas.Intermediate.Store

(* per-epoch aggregated hashes *)
let epoch_hashes = epoch -> ms_hash_value

(* initial epoch hashes - all hashes initialized to 0 (empty_hash_value) *)
val init_epoch_hashes: epoch_hashes

(* update the hash of the epoch ep *)
val upd_epoch_hash (ep2h: epoch_hashes) (ep: epoch) (e: ms_hashfn_dom): epoch_hashes

(* all epochs after a particular epoch have empty hash value *)
let all_epochs_empty_after ep2h ep =
  forall ep'. ep' > ep ==> ep2h ep' = empty_hash_value

(* aggregate epoch hashes upto epoch ep *)
val aggr_epoch_hashes_upto (ep2h: epoch_hashes) (ep: epoch): ms_hash_value

(* Thread-local state
   id     : thread id
   st     : thread local store
   clock  : current timestamp
   hadd   : add set hash
   hevict : evict set hash *)
noeq
type vtls vcfg =
  | Failed : vtls vcfg
  | Valid :
    id : thread_id ->
    st : vstore vcfg ->
    clock : timestamp ->
    hadd : epoch_hashes ->
    hevict : epoch_hashes ->
    vtls vcfg

(* get the store of a specified verifier thread *)
let thread_store #vcfg (vs: vtls vcfg {Valid? vs}): vstore _ =
  Valid?.st vs

let thread_id_of #vcfg (vs:vtls vcfg{Valid? vs}): thread_id =
  Valid?.id vs

let thread_store_size #vcfg (vs: vtls vcfg {Valid? vs}): nat =
  let st = thread_store vs in Seq.length st

let update_thread_store #vcfg (vs:vtls vcfg {Valid? vs}) (st:vstore vcfg) : vtls _ =
  match vs with
  | Valid id _ clock hadd hevict -> Valid id st clock hadd hevict

let thread_clock #vcfg (vs:vtls vcfg {Valid? vs}) =
  Valid?.clock vs

let update_thread_clock #vcfg (vs:vtls vcfg {Valid? vs}) (clock:timestamp): vtls _ =
  match vs with
  | Valid id st _ hadd hevict -> Valid id st clock hadd hevict

let thread_hadd #vcfg (vs:vtls vcfg {Valid? vs}) (ep:epoch): ms_hash_value =
  Valid?.hadd vs ep

let thread_hevict #vcfg (vs:vtls vcfg {Valid? vs}) (ep: epoch): ms_hash_value =
  Valid?.hevict vs ep

let update_thread_hadd #vcfg (vs:vtls vcfg {Valid? vs}) (ep: epoch) (e: ms_hashfn_dom): vtls _ =
  match vs with
  | Valid id st clock hadd hevict ->
    let hadd = upd_epoch_hash hadd ep e in
    Valid id st clock hadd hevict

let update_thread_hevict #vcfg (vs:vtls vcfg {Valid? vs}) (ep: epoch) (e: ms_hashfn_dom): vtls _ =
  match vs with
  | Valid id st clock hadd hevict ->
    let hevict = upd_epoch_hash hevict ep e in
    Valid id st clock hadd hevict

let epoch_of #vcfg (vs: vtls vcfg {Valid? vs}): epoch =
  match vs with
  | Valid _ _ (MkTimestamp ep _) _ _ -> ep

let vget #vcfg (s:slot_id vcfg) (k:data_key) (v:data_value) (vs: vtls vcfg {Valid? vs}) : vtls vcfg =
  let st = thread_store vs in
  (* check slot s is not empty *)
  if empty_slot st s then Failed
  (* check stored key and value *)
  else let k' = stored_key st s in
       let v' = stored_value st s in
       if k <> k' then Failed
       else if to_data_value v' <> v then Failed
       else vs

let vput #vcfg (s:slot_id vcfg) (k:data_key) (v:data_value) (vs: vtls vcfg {Valid? vs}) : vtls vcfg =
  let st = thread_store vs in
  (* check slot s is not empty *)
  if empty_slot st s then Failed
  (* check stored key is k *)
  else let k' = stored_key st s in
       if k <> k' then Failed
       else update_thread_store vs (update_value st s (DVal v))

(* addm params *)
noeq type addm_param (vcfg: verifier_config) =
  | AMP: s: slot_id vcfg ->
         r: record ->
         s': slot_id vcfg ->
         vs': vtls vcfg{Valid? vs'} -> addm_param vcfg

let addm_key #vcfg (a: addm_param vcfg) =
  match a with
  | AMP _ (k,_) _ _ -> k

let addm_slot #vcfg (a: addm_param vcfg) =
  match a with
  | AMP s _ _ _ -> s

let addm_anc_slot #vcfg (a: addm_param vcfg) =
  match a with
  | AMP _ _ s' _ -> s'

let addm_store_pre #vcfg (a: addm_param vcfg) =
  match a with
  | AMP _ _ _ vs' -> thread_store vs'

let addm_precond1 #vcfg (a: addm_param vcfg) =
  let st' = addm_store_pre a in
  match a with
  | AMP s (k,v) s' _ ->
  s <> s' /\
  inuse_slot st' s' /\
  empty_slot st' s /\
  is_value_of k v /\
  (let k' = stored_key st' s' in
   is_proper_desc k k')

let addm_value_pre #vcfg (a: addm_param vcfg {addm_precond1 a}): value_type_of (addm_key a) =
  match a with
  | AMP _ (k,v) _ _ -> v

let addm_hash_val_pre #vcfg (a: addm_param vcfg {addm_precond1 a}) =
  hashfn (addm_value_pre a)

let addm_anc_key #vcfg (a: addm_param vcfg {addm_precond1 a}): merkle_key =
  stored_key (addm_store_pre a) (addm_anc_slot a)

let addm_anc_val_pre #vcfg (a: addm_param vcfg {addm_precond1 a}) =
  let st' = addm_store_pre a in
  let s' = addm_anc_slot a in
  to_merkle_value (stored_value st' s')

let addm_dir #vcfg (a: addm_param vcfg {addm_precond1 a}):bin_tree_dir =
  desc_dir (addm_key a) (addm_anc_key a)

let addm_precond2 #vcfg (a: addm_param vcfg) =
  addm_precond1 a /\
  (let mv' = addm_anc_val_pre a in
   let d = addm_dir a in
   mv_points_to_none mv' d \/                          // case A: ancestor points to nothing along d
   mv_points_to mv' d (addm_key a) \/                  // case B: ancestor points to key being added
   is_proper_desc (mv_pointed_key mv' d) (addm_key a)) // case C: ancestor points to some key below key being added

// case A:
let addm_anc_points_null #vcfg (a: addm_param vcfg{addm_precond2 a}) =
  mv_points_to_none (addm_anc_val_pre a) (addm_dir a)

// case B:
let addm_anc_points_to_key #vcfg (a: addm_param vcfg{addm_precond2 a}) =
  mv_points_to (addm_anc_val_pre a) (addm_dir a) (addm_key a)

// desc hash at ancestor along addm direction
let addm_desc_hash_dir #vcfg (a: addm_param vcfg{addm_precond2 a /\ addm_anc_points_to_key a}) =
  desc_hash_dir (addm_anc_val_pre a) (addm_dir a)

// case C:
let addm_anc_points_to_desc #vcfg (a: addm_param vcfg{addm_precond2 a}) =
  let mv' = addm_anc_val_pre a in
  let d = addm_dir a in
  mv_points_to_some mv' d /\
  is_proper_desc (mv_pointed_key mv' d) (addm_key a)

// desc key for case C:
let addm_desc #vcfg (a:addm_param vcfg{addm_precond2 a /\ addm_anc_points_to_desc a}): (k2:key {is_proper_desc k2 (addm_key a)}) =
  mv_pointed_key (addm_anc_val_pre a) (addm_dir a)

let addm_desc_dir #vcfg (a: addm_param vcfg{addm_precond2 a /\ addm_anc_points_to_desc a}): bin_tree_dir =
  desc_dir (addm_desc a) (addm_key a)

let addm_precond #vcfg (a: addm_param vcfg) =
  let st = addm_store_pre a in
  let s' = addm_anc_slot a in
  addm_precond2 a /\
  (let d = addm_dir a in
   (addm_anc_points_null a ==> (addm_value_pre a = init_value (addm_key a) /\
                              points_to_none st s' d)) /\
   (addm_anc_points_to_key a ==> (addm_desc_hash_dir a = Desc (addm_key a) (addm_hash_val_pre a) false) /\
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

let addm_value_postcond #vcfg (a: addm_param vcfg{addm_precond a}) (v: value_type_of (addm_key a)) =
  (addm_anc_points_null a /\ (v = addm_value_pre a)) \/
  (addm_anc_points_to_key a /\ (v = addm_value_pre a)) \/
  (addm_anc_points_to_desc a /\
    (let dd = addm_desc_dir a in
     let odd = other_dir dd in
     let mv = to_merkle_value v in
     desc_hash_dir mv dd = desc_hash_dir (addm_anc_val_pre a) (addm_dir a) /\
     desc_hash_dir mv odd = Empty))

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
  add_method_of st s = Spec.MAdd /\            // stores the correct add method
  addm_value_postcond a (stored_value st s) /\ // value postcond
  addm_slot_points_postcond a st

let addm_anc_val_postcond #vcfg (a: addm_param vcfg{addm_precond a}) (mv: merkle_value) =
  let mv' = addm_anc_val_pre a in
  let d = addm_dir a in
  let od = other_dir d in
  desc_hash_dir mv od = desc_hash_dir mv' od /\               // merkle value unchanged in other direction
  mv_points_to mv d (addm_key a) /\                           // merkle value points to k in addm direction
  mv_evicted_to_blum mv d = false

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
  stored_key st s' = addm_anc_key a /\
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

let addm_postcond #vcfg (a: addm_param vcfg{addm_precond a}) (vs: vtls vcfg) =
  (* if the precond holds then addm succeeds *)
  Valid? vs /\
  (let Valid id st clk ha he = vs in
   let Valid id' st' clk' ha' he' = AMP?.vs' a in
   id = id' /\ clk = clk' /\ ha == ha' /\ he == he' /\               // everything except store is unchanged
   (addm_has_desc_slot a /\ identical_except3 st st' (addm_slot a) (addm_anc_slot a) (addm_desc_slot a) /\
    addm_desc_slot_postcond a st
    \/
    ~ (addm_has_desc_slot a) /\ identical_except2 st st' (addm_slot a) (addm_anc_slot a)) /\
   addm_slot_postcond a st /\                                      // postcond on slot s
   addm_anc_slot_postcond a st)                                    // postcond on slot s'

val vaddm (#vcfg:verifier_config) (s:slot_id vcfg) (r:record) (s':slot_id vcfg) (vs: vtls vcfg {Valid? vs}):
  (vs': vtls vcfg {let a = AMP s r s' vs in
                   addm_precond a /\ addm_postcond a vs' \/
                   ~(addm_precond a) /\ Failed? vs'})

let vevictm #vcfg (s:slot_id vcfg) (s':slot_id vcfg) (vs: vtls vcfg {Valid? vs}): vtls vcfg =
  let st = thread_store vs in
  (* check store contains s and s' *)
  if empty_slot st s || empty_slot st s' then Failed
  else if s = s' then Failed
  else
    let k = stored_key st s in
    let v = stored_value st s in
    let k' = stored_key st s' in
    let v' = stored_value st s' in
    (* check k is a proper descendent of k' *)
    if not (is_proper_desc k k') then Failed
    (* check k does not have a (merkle) child in the store *)
    else if points_to_some_slot st s Left || points_to_some_slot st s Right then Failed
    else
      let d = desc_dir k k' in
      let v' = to_merkle_value v' in
      let dh' = desc_hash_dir v' d in
      let h = hashfn v in
      match dh' with
      | Empty -> Failed
      | Desc k2 h2 b2 ->
          if k2 <> k then Failed
          (* TODO: explain the following "spurious checks" *)
          (* if s has a parent that is different from s' then Fail *)
          else if has_parent st s && (parent_slot st s <> s' || parent_dir st s <> d) then Failed
          (* if s has no parent, but s' points to something then Fail *)
          else if not (has_parent st s) && (points_to_some_slot st s' d) then Failed
          (* s and s' cannot be the same *)
          else if s = s' then Failed
          else
            let v'_upd = Spec.update_merkle_value v' d k h false in
            let st_upd = update_value st s' (MVal v'_upd) in
            let st_upd = mevict_from_store st_upd s s' d in
            update_thread_store vs st_upd

let vaddb #vcfg (s:slot_id vcfg) (r:record) (t:timestamp) (j:thread_id) (vs:vtls _ {Valid? vs}): vtls _ =
  let st = thread_store vs in
  let (k,v) = r in
  (* check value type consistent with key k *)
  if not (is_value_of k v) then Failed
  (* check store contains slot s *)
  else if inuse_slot st s then Failed
  else
    (* the record was previously evicted in epoch ep *)
    let MkTimestamp ep c = t in

    (* update add hash *)
    let vs_upd = update_thread_hadd vs ep (MHDom (k,v) t j) in

    (* update clock *)
    let clk = thread_clock vs in
    let clk_upd = Spec.max clk (next t) in
    let vs_upd = update_thread_clock vs_upd clk_upd in

    (* add record to store *)
    let st_upd = badd_to_store st s k v in
    update_thread_store vs_upd st_upd

let sat_evictb_checks #vcfg (s:slot_id vcfg) (t:timestamp) (vs:vtls _ {Valid? vs}): bool =
  let st = thread_store vs in
  inuse_slot st s &&
  (
    let k = stored_key st s in
    let v = stored_value st s in
    let clock = thread_clock vs in

    (* check key at s is not root *)
    k <> Root &&

    (* check time of evict < current time *)
    clock `ts_lt` t &&

    (* check k has no (merkle) children n the store *)
    points_to_none st s Left && points_to_none st s Right
  )

let vevictb_update_hash_clock #vcfg (s:slot_id vcfg) (t:timestamp) (vs:vtls _ {Valid? vs /\ sat_evictb_checks s t vs}):
  (vs':vtls _ {Valid? vs'}) =

  let st = thread_store vs in
  let k = stored_key st s in
  let v = stored_value st s in

  let MkTimestamp ep _ = t in

  (* update evict hash *)
  let vs_upd = update_thread_hevict vs ep (MHDom (k,v) t (thread_id_of vs))  in

  (* update clock and return *)
  update_thread_clock vs_upd t

let vevictb #vcfg (s:slot_id vcfg) (t:timestamp) (vs:vtls _ {Valid? vs}): vtls _ =
  let st = thread_store vs in
  if not (sat_evictb_checks s t vs) || add_method_of st s <> Spec.BAdd then Failed
  else
    let k = stored_key st s in
    let v = stored_value st s in
    let vs = vevictb_update_hash_clock s t vs in
    let st_upd = bevict_from_store st s in
    update_thread_store vs st_upd

let vevictbm #vcfg (s:slot_id vcfg) (s':slot_id vcfg) (t:timestamp) (vs:vtls vcfg {Valid? vs}): vtls vcfg =
  let st = thread_store vs in
  if s = s' then Failed
  else if not (sat_evictb_checks s t vs) || add_method_of st s <> Spec.MAdd then Failed
  else if empty_slot st s' then Failed
  else
    let k = stored_key st s in
    let k' = stored_key st s' in
    let v' = stored_value st s' in
    (* check k is a proper desc of k' *)
    if not (is_proper_desc k k') then Failed
    else
      let v' = to_merkle_value v' in
      let d = desc_dir k k' in
      let dh' = desc_hash_dir v' d in
      match dh' with
      | Empty -> Failed
      | Desc k2 h2 b2 ->
          if k2 <> k || b2 then Failed
          else if not (has_parent st s) || parent_slot st s <> s' || parent_dir st s <> d then Failed
          else
            (* update the evict hash and the clock *)
            let vs = vevictb_update_hash_clock s t vs in
            // assert(thread_store vs == thread_store vs_upd);

            (* update the hash at k' *)
            let v'_upd = Spec.update_merkle_value v' d k h2 true in
            let st = update_value st s' (MVal v'_upd) in

            (* evict s' from store *)
            let st = mevict_from_store st s s' d in
            update_thread_store vs st

let vnext_epoch #vcfg (vs: vtls vcfg{Valid? vs}): vtls _ =
  let MkTimestamp ep _ = thread_clock vs in
  let clk = MkTimestamp (ep + 1) 0 in
  update_thread_clock vs clk

let verify_step #vcfg (vs:vtls vcfg) (e:logS_entry vcfg): vtls vcfg =
  match vs with
  | Failed -> Failed
  | _ ->
    match e with
    | Get_S s k v -> vget s k v vs
    | Put_S s k v -> vput s k v vs
    | AddM_S s r s' -> vaddm s r s' vs
    | EvictM_S s s' -> vevictm s s' vs
    | AddB_S s r t j -> vaddb s r t j vs
    | EvictB_S s t -> vevictb s t vs
    | EvictBM_S s s' t -> vevictbm s s' t vs
    | NextEpoch -> vnext_epoch vs
    | VerifyEpoch -> vs (* no op *)

(* once we hit a failed state, we remain there *)
val lemma_verify_failed (#vcfg:_) (vs:vtls vcfg) (e:_)
  : Lemma (requires (Failed? vs))
          (ensures (Failed? (verify_step vs e)))

let rec verify #vcfg (vsinit:vtls vcfg) (l:logS vcfg): Tot (vtls vcfg)
  (decreases (Seq.length l)) =
  let n = Seq.length l in
  if n = 0 then vsinit
  else
    let lp = prefix l (n - 1) in
    let vsp = verify vsinit lp in
    let e = Seq.index l (n - 1) in
    verify_step vsp e

let verifiable #vcfg (vsinit:vtls vcfg) (l:logS _) =
  Valid? (verify vsinit l)

(* if a log is verifiable with some initial state, then that state should be valid *)
val lemma_verifiable_implies_init_valid (#vcfg:_) (vsinit: vtls vcfg) (l: logS _):
  Lemma (requires (verifiable vsinit l))
        (ensures (Valid? vsinit))
        [SMTPat (verifiable vsinit l)]

(* if a log is verifiable then the prefix of the log is verifiable *)
val lemma_verifiable_implies_prefix_verifiable
      (#vcfg:_)
      (vsinit: vtls vcfg)
      (l: logS _{verifiable vsinit l})
      (i: seq_index l):
  Lemma (ensures (let li = prefix l i in
                  verifiable vsinit li))
        [SMTPat (verifiable vsinit (prefix l i))]

val lemma_addm_props (#vcfg:_)
                     (vs:vtls vcfg{Valid? vs})
                     (e:logS_entry _{AddM_S? e}):
  Lemma (requires (Valid? (verify_step vs e)))
        (ensures (let AddM_S s (k,v) s' = e in
                  let st' = thread_store vs in
                  inuse_slot st' s' /\
                  (let k' = stored_key st' s' in
                   is_proper_desc k k' /\
                   is_merkle_key k' /\
                   (let mv' = to_merkle_value (stored_value st' s') in
                    let d = desc_dir k k' in
                    (mv_points_to_none mv' d ||
                     is_desc (mv_pointed_key mv' d) k)))))

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

(* Relation between thread-local states
   * either both states have Failed
   * or both are Valid with equal contents
     (note that store_rel st st' enforces is_map st) *)
let vtls_rel #vcfg (vs:vtls vcfg) (vs':Spec.vtls) : Type =
  (Failed? vs /\ Spec.Failed? vs') \/
  (Valid? vs /\ Spec.Valid? vs' /\
   (let Valid id st clk ha he = vs in
    let Spec.Valid id' st' clk' _ ha' he' _ = vs' in
    let MkTimestamp ep _ = clk in
    let ha = aggr_epoch_hashes_upto ha ep in
    let he = aggr_epoch_hashes_upto he ep in
    store_rel st st' /\ id = id' /\ clk = clk' /\ ha = ha' /\ he = he'))

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


let init_thread_state #vcfg (tid:thread_id) (st:vstore _): vtls vcfg =
  Valid tid st (MkTimestamp 0 0) init_epoch_hashes init_epoch_hashes

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
