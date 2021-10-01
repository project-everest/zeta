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
#push-options "--fuel 2 --ifuel 1" // some proofs need fuel 2; because of needing to unroll t_of
noeq
type prf_set_hash = {
  ha_state : HA.ha;
  serialization_buf: a:A.array U8.t{A.length a == 184 }
}

let prf_set_hash_vprop (s:prf_set_hash)
  : vprop
  = HA.ha_inv s.ha_state `star`
    A.varray s.serialization_buf

let prf_set_hash_sl (s:prf_set_hash)
  : slprop u#1
  = hp_of (prf_set_hash_vprop s)

let prf_set_hash_repr
  : Type0
  = (HA.ha_repr & A.contents U8.t 184)

let hash_value_of (p:prf_set_hash_repr) = HA.value_of (fst p)

let prf_set_hash_sel (r:prf_set_hash)
  : GTot (selector prf_set_hash_repr (prf_set_hash_sl r))
  = sel_of (prf_set_hash_vprop r)

let intro_set_hash_inv #o (s:prf_set_hash)
  : SteelGhost unit o
    (HA.ha_inv s.ha_state `star` A.varray s.serialization_buf)
    (fun _ -> prf_set_hash_inv s)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      v_hash s h1 == HA.hash_value_of s.ha_state h0)
  = AT.change_slprop_rel (HA.ha_inv s.ha_state `star` A.varray s.serialization_buf)
                         (prf_set_hash_inv s)
                         (fun x y -> x == y)
                         (fun m -> ())

let elim_set_hash_inv #o (s:prf_set_hash)
  : SteelGhost unit o
    (prf_set_hash_inv s)
    (fun _ -> HA.ha_inv s.ha_state `star` A.varray s.serialization_buf)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      v_hash s h0 == HA.hash_value_of s.ha_state h1)
  = AT.change_slprop_rel (prf_set_hash_inv s)
                         (HA.ha_inv s.ha_state `star` A.varray s.serialization_buf)
                         (fun x y -> x == y)
                         (fun m -> ())

let create x =
  let buf = A.malloc 0uy 184ul in
  let res = {
    ha_state = x;
    serialization_buf = buf
  } in
  AT.change_equal_slprop (HA.ha_inv x `star` A.varray buf)
                         (HA.ha_inv res.ha_state `star` A.varray res.serialization_buf);
  intro_set_hash_inv res;
  AT.return res

let free (p:prf_set_hash)
  = elim_set_hash_inv p;
    A.free p.serialization_buf;
    AT.return p.ha_state

let prf_update_hash' (p:HA.ha)
                     (r:T.record)
                     (t:T.timestamp)
                     (tid:T.thread_id)
                     (buf:A.array U8.t)
  : Steel bool
    (HA.ha_inv p `star` A.varray buf)
    (fun _ -> HA.ha_inv p `star` A.varray buf)
    (requires fun _ ->
      A.length buf == 184)
    (ensures fun h0 b h1 ->
      HA.hash_value_of p h1 ==
      maybe_update_hash_value b (HA.hash_value_of p h0) r t tid)
  =  let h0 = AT.get () in
     let sr = (VFT.({ sr_record = r; sr_timestamp = t; sr_thread_id = tid})) in
     let len = VF.serialize_stamped_record buf sr in
     let h1 = AT.get () in
     let b = HA.add p buf len in
     let h2 = AT.get () in
     assert (HA.hash_value_of p h2 ==
             HA.maybe_aggregate_hashes
                 b
                 (HA.hash_value_of p h1)
                 (HA.hash_one_value
                   (Seq.slice (A.asel buf h1) 0 (U32.v len))));
     assert (Seq.slice (A.asel buf h1) 0 (U32.v len) ==
             VF.serialize_stamped_record_spec sr);
     assert (HA.hash_value_of p h2 ==
             HA.maybe_aggregate_hashes b
               (HA.hash_value_of p h1)
               (HA.hash_one_value (VF.serialize_stamped_record_spec sr)));
     AT.return b

let prf_update_hash p r t tid =
  elim_set_hash_inv p;
  let b = prf_update_hash' p.ha_state r t tid p.serialization_buf in
  intro_set_hash_inv p;
  AT.return b
