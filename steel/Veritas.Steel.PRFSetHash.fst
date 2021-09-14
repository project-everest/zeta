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
module AT = Steel.Effect.Atomic
module VFT = Veritas.Formats.Types
module VF = Veritas.Formats
module MSH = Veritas.MultiSetHash
module HA = Veritas.Steel.HashAccumulator

let prf_set_hash = HA.state

let prf_set_hash_sl (s:prf_set_hash)
  : slprop u#1
  = A.is_array s

let prf_set_hash_sel (r:prf_set_hash)
  : selector (HA.hash_value_t) (prf_set_hash_sl r)
  = A.array_sel r

let create () =
  let x = HA.create_in () in
  AT.change_equal_slprop (A.varray _)
                         (prf_set_hash_inv _);
  AT.return x

let free (p:prf_set_hash)
  = AT.change_equal_slprop (prf_set_hash_inv _)
                           (A.varray _);
    HA.free p

let update_hash_value (ha:HA.hash_value_t)
                      (r:T.record)
                      (t:T.timestamp)
                      (tid:T.thread_id)
  : GTot HA.hash_value_t
  = let b = VF.serialize_stamped_record_spec (VFT.({ sr_record = r; sr_timestamp = t; sr_thread_id = tid})) in
    let h = HA.hash_value b in
    HA.aggregate_hash_value ha h

#push-options "--query_stats"
let prf_update_hash' (p:prf_set_hash)
                     (r:T.record)
                     (t:T.timestamp)
                     (tid:T.thread_id)
  : Steel unit
    (A.varray p)
    (fun _ -> A.varray p)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel p h1 == update_hash_value (A.asel p h0) r t tid)
  =  let h0 = AT.get () in
     let sr = (VFT.({ sr_record = r; sr_timestamp = t; sr_thread_id = tid})) in
     let tmp = A.malloc 0uy 184ul in
     let len = VF.serialize_stamped_record tmp sr in
     let h1 = AT.get () in
     HA.add p tmp len;
     A.free tmp;
     AT.slassert (A.varray p);
     let h2 = AT.get () in
     assert (A.asel p h2 ==
             HA.aggregate_hash_value (A.asel p h1)
                                     (HA.hash_value
                                       (Seq.slice (A.asel tmp h1) 0 (U32.v len))));
     assert (Seq.slice (A.asel tmp h1) 0 (U32.v len) ==
             VF.serialize_stamped_record_spec sr);
     assert (A.asel p h2 ==
             HA.aggregate_hash_value
               (A.asel p h1)
               (HA.hash_value (VF.serialize_stamped_record_spec sr)));
     assert_spinoff (A.asel p h2 ==
                     update_hash_value (A.asel p h1) r t tid)

let prf_update_hash p r t tid =
  AT.change_equal_slprop (prf_set_hash_inv p)
                         (A.varray p);
  prf_update_hash' p r t tid;
  AT.change_equal_slprop (A.varray p)
                         (prf_set_hash_inv p)

let prf_read_hash' (p:prf_set_hash) (out:A.array U8.t)
  : Steel unit
    (A.varray p `star` A.varray out)
    (fun _ -> A.varray p `star` A.varray out)
    (requires fun _ -> A.length out == 32)
    (ensures fun h0 _ h1 ->
      A.length out == 32 /\
      A.asel p h0 == A.asel p h1 /\
      A.asel out h1 == A.asel p h1)
  = HA.get p out

let prf_read_hash (p:prf_set_hash) (out:A.array U8.t)
  = AT.change_equal_slprop (prf_set_hash_inv p)
                           (A.varray p);
    prf_read_hash' p out;
    AT.change_equal_slprop (A.varray p)
                           (prf_set_hash_inv p)

let prf_hash_agg (a0 a1:A.array U8.t)
  : Steel unit
    (A.varray a0 `star` A.varray a1)
    (fun _ -> A.varray a0 `star` A.varray a1)
    (requires fun _ ->
      A.length a0 == 32 /\
      A.length a1 == 32)
    (ensures fun h0 _ h1 ->
      A.length a0 == 32 /\
      A.length a1 == 32 /\
      A.asel a1 h0 == A.asel a1 h1 /\
      A.asel a0 h1 ==
        HA.aggregate_hash_value (A.asel a0 h0) (A.asel a1 h0))
  = HA.aggregate_hash_value_buf a0 a1
