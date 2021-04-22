module Veritas.SteelSel.Verifier

open Steel.Memory
open Steel.SelEffect
open Steel.SelArray
open FStar.Ghost
module U32 = FStar.UInt32
module U64 = FStar.UInt64
// open Veritas.SteelSel.VCache
// open Veritas.Steel.Types

module K = Veritas.Key
module R = Veritas.Record
module L = Veritas.Intermediate.Logs
module S = Veritas.Intermediate.Store
module V = Veritas.Intermediate.Verify
module VC = Veritas.Intermediate.VerifierConfig
module MS = Veritas.MultiSetHashDomain

#set-options "--ide_id_info_off"

(** Definition of the low-level thread state datatype **)

// AF: Some assumed types for low-level versions of intermediate types
val data_key_t: Type0
val key_v (k:data_key_t) : K.data_key
val data_value_t: Type0
val value_v (v:data_value_t) : R.data_value

(* Low-level definition of slot_id *)
let slot_t (vcfg:VC.verifier_config) = (i:U32.t{U32.v i < VC.store_size vcfg})

// AF: Temporary placeholder for low-level clock.
// Should be replaced by the appropriate low-level type
let timestamp_t = ref MS.timestamp

// AF: Placeholder for low-level version of the thread local store
val vstore_t (vcfg:VC.verifier_config) : Type0
// AF: This will be implemented as an array.
// But it also needs to encapsulate the invariants to provide a selector to store
// instead of store_raw
// A simple way would be to add those as pure predicates in the slprop, but
// an easier mechanism for selector invariants/refinements would be useful
val vstore_sl (#vcfg:_) (st:vstore_t vcfg) : slprop u#1
val vstore_sel (#vcfg:_) (st:vstore_t vcfg) : selector (S.vstore vcfg) (vstore_sl st)
[@@__steel_reduce__]
let is_vstore' #vcfg (st:vstore_t vcfg) : vprop' =
  { hp = vstore_sl st;
    t = S.vstore vcfg;
    sel = vstore_sel st }
unfold
let is_vstore #vcfg (st:vstore_t vcfg) : vprop = VUnit (is_vstore' st)
[@@ __steel_reduce__]
let v_st (#p:vprop) (#vcfg:_) (st:vstore_t vcfg)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (is_vstore st) /\ True)})
  : GTot (S.vstore vcfg)
  = h (is_vstore st)

val vstore_get_record (#vcfg:_) (st:vstore_t vcfg) (s:slot_t vcfg)
  : SteelSel
      (option (S.vstore_entry vcfg))
      (is_vstore st)
      (fun _ -> is_vstore st)
      (requires fun h -> True)
      (ensures fun h0 res h1 ->
        // Framing
        v_st st h0 == v_st st h1 /\
        // Functional correctness
        res == Seq.index (v_st st h1) (U32.v s))

val vstore_update_record (#vcfg:_) (st:vstore_t vcfg) (s:slot_t vcfg) (r:data_value_t)
  : SteelSel unit
      (is_vstore st)
      (fun _ -> is_vstore st)
      (requires fun h0 ->
        S.inuse_slot (v_st st h0) (U32.v s) /\
        K.is_data_key (S.stored_key (v_st st h0) (U32.v s)))
      (ensures fun h0 _ h1 ->
        S.inuse_slot (v_st st h0) (U32.v s) /\
        K.is_data_key (S.stored_key (v_st st h0) (U32.v s)) /\
        // Functional correctness
        v_st st h1 == S.update_value (v_st st h0) (U32.v s) (R.DVal (value_v r)))


// AF: Placeholder for the low-level version of the multiset hash
val prf_set_hash : Type0
// AF: Internally, should probably be implemented with a ghost reference to the model_hash
// The selector would then fetch the value in the ghost state
// The reason why we would need a ghost state is that the "spec" contains strictly more
// information than the concrete value. So we cannot reconstruct it out of just the concrete state
val prf_set_hash_sl (_:prf_set_hash) : slprop u#1
val prf_set_hash_sel (r:prf_set_hash) : selector MS.ms_hash_value (prf_set_hash_sl r)
[@@__steel_reduce__]
let prf_set_hash_inv' (r:prf_set_hash) : vprop' =
  { hp = prf_set_hash_sl r;
    t = MS.ms_hash_value;
    sel = prf_set_hash_sel r}
unfold
let prf_set_hash_inv (r:prf_set_hash) : vprop = VUnit (prf_set_hash_inv' r)

(* Standard Steel helper to access the selector of the hash without repeating the slprop *)
[@@ __steel_reduce__]
let v_hash (#p:vprop) (r:prf_set_hash)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (prf_set_hash_inv r) /\ True)})
  : GTot MS.ms_hash_value
  = h (prf_set_hash_inv r)

(* Low-level struct representing the current state of a thread *)
noeq
type thread_state_t vcfg = {
  failed       : ref bool;
  id           : L.thread_id;
  st           : vstore_t vcfg;  //a map from keys (cache ids) to merkle leaf or internal nodes
  clock        : timestamp_t;
  hadd         : prf_set_hash; //current incremental set hash values; TODO
  hevict       : prf_set_hash;
}

(* The separation logic assertion representing the validity of the thread state *)
[@@__reduce__; __steel_reduce__]
let thread_state_inv #vcfg (t:thread_state_t vcfg) : vprop =
  is_vstore t.st `star`
  vptr t.clock `star`
  vptr t.failed `star`
  prf_set_hash_inv t.hadd `star`
  prf_set_hash_inv t.hevict


(* An abstraction on top of the thread selector state to match with the intermediate
   thread state representation *)
[@@ __steel_reduce__]
unfold
let v_thread (#p:vprop) (#vcfg:_) (t:thread_state_t vcfg)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (thread_state_inv t) /\ True)})
  : GTot (V.vtls vcfg)
  = if sel t.failed (focus_rmem h (thread_state_inv t)) then
      V.Valid
        t.id
        (v_st t.st (focus_rmem h (thread_state_inv t)))
        (sel t.clock (focus_rmem h (thread_state_inv t)))
        (v_hash t.hadd (focus_rmem h (thread_state_inv t)))
        (v_hash t.hevict (focus_rmem h (thread_state_inv t)))
    else V.Failed


(* Updates the thread state to a Failed state *)
let fail #vcfg (vs:thread_state_t vcfg) (msg:string)
  // AF: We put it in SteelSelF to avoid simplify its use in branches because we currently
  // cannot have SteelSel and SteelSelF branches at the same time, but it shouldn't be
  : SteelSelF unit
             (thread_state_inv vs)
             (fun _ -> thread_state_inv vs)
             (requires fun _ -> True)
             (ensures fun _ _ h1 -> v_thread vs h1 == V.Failed)
  = // AF: Need trailing unit to trigger framing. Will be solved once we have framing subcomp
    write vs.failed false; ()

(* An implementation of Veritas.Intermediate.Verify.vget *)
let vget (#vcfg:_) (s:slot_t vcfg) (k:data_key_t) (v:data_value_t) (vs:thread_state_t vcfg)
  : SteelSel unit
             (thread_state_inv vs)
             (fun _ -> thread_state_inv vs)
             (requires fun h0 ->
               V.Valid? (v_thread vs h0))
             (ensures fun h0 _ h1 ->
               V.Valid? (v_thread vs h0) /\
               v_thread vs h1 == V.vget (U32.v s) (key_v k) (value_v v) (v_thread vs h0)
             )
  = // AF: Still unclear why this is needed
    let h = get () in
    assert (V.Valid? (v_thread vs h));

    let r0 = vstore_get_record vs.st s in
    match r0 with
    | None -> fail vs "VGet: Empty slot"
    | Some r' ->
      let k' = S.VStoreE?.k r' in
      let v' = S.VStoreE?.v r' in
      if key_v k <> k' then fail vs "VGet: Key mismatch"
      else if R.to_data_value v' <> value_v v then fail vs "VGet: Value mismatch"
      // AF: Usual problem of Steel vs SteelSel difference in branches
      else (noop (); ())


(* An implementation of Veritas.Intermediate.Verify.vput *)
let vput (#vcfg:_) (s:slot_t vcfg) (k:data_key_t) (v:data_value_t) (vs:thread_state_t vcfg)
  : SteelSel unit
             (thread_state_inv vs)
             (fun _ -> thread_state_inv vs)
             (requires fun h0 ->
               V.Valid? (v_thread vs h0))
             (ensures fun h0 _ h1 ->
               V.Valid? (v_thread vs h0) /\
               v_thread vs h1 == V.vput (U32.v s) (key_v k) (value_v v) (v_thread vs h0)
               )
  = // AF: Still unclear why this is needed
    let h = get () in
    assert (V.Valid? (v_thread vs h));

    let r0 = vstore_get_record vs.st s in
    match r0 with
    | None -> fail vs "VPut: Empty slot"
    | Some r' ->
      let k' = S.VStoreE?.k r' in
      if key_v k <> k' then fail vs "VPut: Key mismatch"
      // AF: Need the trailing unit to put the body of the else branch into SteelSelF
      // which is needed since both branches of an if/then/else currently need the same effect
      else (vstore_update_record vs.st s v; ())
