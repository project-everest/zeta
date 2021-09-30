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
#push-options "--query_stats"
#push-options "--fuel 2 --ifuel 1" //not sure why some proofs need fuel 2
noeq
type prf_set_hash = {
  ha_state : HA.state;
  serialization_buf: a:A.array U8.t{A.length a == 184 }
}

let prf_set_hash_vprop (s:prf_set_hash)
  : vprop
  = A.varray s.ha_state `star`
    A.varray s.serialization_buf

let prf_set_hash_sl (s:prf_set_hash)
  : slprop u#1
  = hp_of (prf_set_hash_vprop s)

let prf_set_hash_repr
  : Type0
  = (HA.hash_value_t & A.contents U8.t 184)

let hash_value_of (p:prf_set_hash_repr) = fst p

let prf_set_hash_sel (r:prf_set_hash)
  : GTot (selector prf_set_hash_repr (prf_set_hash_sl r))
  = sel_of (prf_set_hash_vprop r)

let intro_set_hash_inv #o (s:prf_set_hash)
  : SteelGhost unit o
    (A.varray s.ha_state `star` A.varray s.serialization_buf)
    (fun _ -> prf_set_hash_inv s)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      v_hash s h1 == A.asel s.ha_state h0)
  = AT.change_slprop_rel (A.varray s.ha_state `star` A.varray s.serialization_buf)
                         (prf_set_hash_inv s)
                         (fun x y -> x == y)
                         (fun m -> ())

let elim_set_hash_inv #o (s:prf_set_hash)
  : SteelGhost unit o
    (prf_set_hash_inv s)
    (fun _ -> A.varray s.ha_state `star` A.varray s.serialization_buf)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      v_hash s h0 == A.asel s.ha_state h1)
  = AT.change_slprop_rel (prf_set_hash_inv s)
                         (A.varray s.ha_state `star` A.varray s.serialization_buf)
                         (fun x y -> x == y)
                         (fun m -> ())

let create () =
  let x = HA.create_in () in
  let buf = A.malloc 0uy 184ul in
  let res = {
    ha_state = x;
    serialization_buf = buf
  } in
  AT.change_equal_slprop (A.varray x `star` A.varray buf)
                         (A.varray res.ha_state `star` A.varray res.serialization_buf);
  intro_set_hash_inv res;
  AT.return res

let free (p:prf_set_hash)
  = elim_set_hash_inv p;
    HA.free p.ha_state;
    A.free p.serialization_buf

//#push-options "--query_stats"
let prf_update_hash' (p:HA.state)
                     (r:T.record)
                     (t:T.timestamp)
                     (tid:T.thread_id)
                     (buf:A.array U8.t)
  : Steel unit
    (A.varray p `star` A.varray buf)
    (fun _ -> A.varray p `star` A.varray buf)
    (requires fun _ ->
      A.length p == 32 /\
      A.length buf == 184)
    (ensures fun h0 _ h1 ->
      A.asel p h1 == VM.update_hash_value (A.asel p h0) r t tid)
  =  let h0 = AT.get () in
     let sr = (VFT.({ sr_record = r; sr_timestamp = t; sr_thread_id = tid})) in
     let len = VF.serialize_stamped_record buf sr in
     let h1 = AT.get () in
     HA.add p buf len;
     AT.slassert (A.varray p);
     let h2 = AT.get () in
     assert (A.asel p h2 ==
             HA.aggregate_hash_value (A.asel p h1)
                                     (HA.hash_value
                                       (Seq.slice (A.asel buf h1) 0 (U32.v len))));
     assert (Seq.slice (A.asel buf h1) 0 (U32.v len) ==
             VF.serialize_stamped_record_spec sr);
     assert (A.asel p h2 ==
             HA.aggregate_hash_value
               (A.asel p h1)
               (HA.hash_value (VF.serialize_stamped_record_spec sr)));
     assert_spinoff (A.asel p h2 ==
                     VM.update_hash_value (A.asel p h1) r t tid)

let prf_update_hash p r t tid =
  elim_set_hash_inv p;
  prf_update_hash' p.ha_state r t tid p.serialization_buf;
  intro_set_hash_inv p

let prf_read_hash' (p:HA.state) (out:A.array U8.t)
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
  = elim_set_hash_inv p;
    prf_read_hash' p.ha_state out;
    intro_set_hash_inv p

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
