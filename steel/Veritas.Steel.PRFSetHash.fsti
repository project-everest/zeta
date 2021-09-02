module Veritas.Steel.PRFSetHash

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
open Steel.Array
open FStar.Ghost
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module T = Veritas.Formats.Types
open Veritas.Steel.VerifierModel
open Veritas.ThreadStateModel
val prf_set_hash : Type0

// AF: Internally, should probably be implemented with a ghost reference to the model_hash
// The selector would then fetch the value in the ghost state
// The reason why we would need a ghost state is that the "spec" contains strictly more
// information than the concrete value. So we cannot reconstruct it out of just the concrete state
val prf_set_hash_sl (_:prf_set_hash) : slprop u#1
val prf_set_hash_sel (r:prf_set_hash) : selector (model_hash) (prf_set_hash_sl r)

[@@__steel_reduce__]
noextract
let prf_set_hash_inv' (r:prf_set_hash) : vprop' =
  { hp = prf_set_hash_sl r;
    t = model_hash;
    sel = prf_set_hash_sel r}

unfold
let prf_set_hash_inv (r:prf_set_hash) : vprop = VUnit (prf_set_hash_inv' r)

[@@ __steel_reduce__]
let v_hash (#p:vprop) (r:prf_set_hash)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (prf_set_hash_inv r) /\ True)})
  : GTot model_hash
  = h (prf_set_hash_inv r)

val create (_:unit)
  : Steel prf_set_hash
    emp
    (fun p -> prf_set_hash_inv p)
    (requires fun _ -> True)
    (ensures fun _ p h1 -> v_hash p h1 == init_hash)

val free (p:prf_set_hash)
  : SteelT unit
    (prf_set_hash_inv p)
    (fun _ -> emp)

val prf_update_hash (p:prf_set_hash) (r:T.record) (t:T.timestamp) (thread_id:T.thread_id)
  : Steel unit
    (prf_set_hash_inv p)
    (fun _ -> prf_set_hash_inv p)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> v_hash p h1 == model_update_hash (v_hash p h0) r t thread_id)

module A = Steel.Array
module U8 = FStar.UInt8

val as_model_hash (s:Seq.lseq U64.t 4) : model_hash
val prf_read_hash (p:prf_set_hash) (out:A.array U64.t)
  : Steel unit
    (prf_set_hash_inv p `star` A.varray out)
    (fun _ -> prf_set_hash_inv p `star` A.varray out)
    (requires fun _ -> A.length out == 4)
    (ensures fun h0 _ h1 ->
      A.length out == 4 /\
      v_hash p h0 == v_hash p h1 /\
      as_model_hash (A.asel out h1) == v_hash p h1)
