module Veritas.MultiSetHash

open FStar.BitVector
open FStar.Seq
open Veritas.Key
open Veritas.MultiSet
open Veritas.Record
open Veritas.SeqAux
include Veritas.MultiSetHashDomain
module T = Veritas.Formats.Types
module VF = Veritas.Formats
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module L = FStar.List.Tot.Properties
open Veritas.BinTree
open FStar.Mul
module BV = FStar.BV
module HA = Veritas.Steel.HashAccumulator

(* This module specifies a hash on a sequence of ms_hasfn_dom entries.

   Concretely, it corresponds on part of its domain to the hash
   function implemented in Veritas.Steel.PRFSetHash

   However ms_hashfn_dom is a larger type than the domain of
   Veritas.Steel.PRFSetHash. In particular, ms_hashfn_dom includes

     - arbitrary integers in data values (whereas in the Steel code,
       values are just u256)

     - arbitrary natural numbers for timestamp and epoch counts
       (whereas in Steel, each is only 32 bits)

     - arbitrary natural numbers of thread ids (whereas in Steel they
       are a u16)

     So, for ms_hashfn_dom elements that do not meet these bounds, we
     rely on unspecified_hash_function. Otherwise, we use what is
     specified by PRFSetHash.

     This "overspecification" of the hash on the full domain of
     ms_hashfn_dom doesn't hurt us, since eventually, we will only
     relate the low-level hashes computed on the sub-domain of values
     of ms_hashfn_dom that are represented in Steel.

*)
assume
val unspecified_hash_function (e: ms_hashfn_dom)
  : Tot HA.hash_value_t

(* A total serializer for stamped records
   -- This assumption is a technicality.

      The serializer spec produced by EverParse is in the GTot
      effect. Whereas we want a Tot serializer here ... or else we
      could move the entire high and intermediate development to
      GTot. Which would be fine too but is a big syntactic change.

      Instead, we assume a total serializer that is extensionally
      equal to the EverParse serializer spec
*)
assume
val serializer (e:T.stamped_record)
  : Tot (s:seq UInt8.t{ s == VF.serialize_stamped_record_spec e })

[@@"opaque_to_smt"]
let lseq8_to_u8 (l:lseq bool 8)
  : U8.t
  = U8.uint_to_t (BV.bv2int (FStar.BV.list2bv (Seq.seq_to_list l)))

[@@"opaque_to_smt"]
let lseq64_to_u64 (s:lseq bool 64)
  : U64.t
  = U64.uint_to_t (BV.bv2int (BV.list2bv (seq_to_list s)))

[@@"opaque_to_smt"]
let lseq256_as_u256 (l:lseq bool 256)
  : T.u256
  = let v3, rest = Seq.split l 64 in
    let v2, rest = Seq.split rest 64 in
    let v1, v0 = Seq.split rest 64 in
    {
      v3 = lseq64_to_u64 v3;
      v2 = lseq64_to_u64 v2;
      v1 = lseq64_to_u64 v1;
      v0 = lseq64_to_u64 v0
    }

[@@"opaque_to_smt"]
let rec bv_to_lseq_u8 (#n:nat) (l:lseq bool (8 * n))
  : lseq U8.t n
  = if n = 0 then Seq.empty
    else let h, rest = Seq.split l 8 in
         Seq.cons (lseq8_to_u8 h) (bv_to_lseq_u8 #(n - 1) rest)

[@@"opaque_to_smt"]
let rec lseq_u8_to_bv (#n:nat) (l:lseq U8.t n)
  : lseq bool (8 * n)
  = if n = 0 then Seq.empty
    else let hd = Seq.seq_of_list (BV.bv2list (BV.int2bv #8 (U8.v (Seq.head l)))) in
         Seq.append hd (lseq_u8_to_bv #(n - 1) (Seq.tail l))

[@@"opaque_to_smt"]
let rec key_as_seq (k:key)
  : lseq bool (depth k)
  = match k with
    | Root -> Seq.empty
    | LeftChild k' -> Seq.snoc (key_as_seq k') false
    | RightChild k' -> Seq.snoc (key_as_seq k') true

[@@"opaque_to_smt"]
let key_as_lseq_256 (k:key)
  : lseq bool 256
  = let s = key_as_seq k in
    let pad = Seq.create (256 - depth k) false in
    Seq.append pad s

[@@"opaque_to_smt"]
let key_as_u256 (k:key)
  : Tot T.u256
  = lseq256_as_u256 (key_as_lseq_256 k)

let as_key (k:key)
  : T.key
  = { k = key_as_u256 k;
      significant_digits = FStar.UInt16.uint_to_t (depth k) }

let hash_value_as_hash_value (h:hash_value)
  : T.hash_value
  = lseq256_as_u256 h

let desc_hash_as_descendent_hash (dh:desc_hash)
  : T.descendent_hash
  = match dh with
    | Empty -> T.Dh_vnone ()
    | Desc k v b ->
      let k = as_key k in
      let v = hash_value_as_hash_value v in
      T.Dh_vsome T.({ dhd_key = k; dhd_h = v; evicted_to_blum = if b then Vtrue else Vfalse })

let merkle_value_as_mval_value (mv:merkle_value)
  : T.mval_value
  = { l = desc_hash_as_descendent_hash mv.l;
      r = desc_hash_as_descendent_hash mv.r }

[@@"opaque_to_smt"]
let data_value_as_data_value (mv:data_value)
  : option T.data_value
  = match mv with
    | Null -> Some (T.Dv_vnone ())
    | DValue i ->
      if 0 <= i && i < pow2 256
      then Some (T.Dv_vsome (lseq256_as_u256 (Seq.seq_of_list (BV.bv2list (BV.int2bv #256 i)))))
      else None

let as_value (v:value)
  : option T.value
  = match v with
    | MVal mv ->
      Some (T.V_mval (merkle_value_as_mval_value mv))
    | DVal v ->
      let vopt = data_value_as_data_value v in
      match vopt with
      | Some v -> Some (T.V_dval v)
      | _ -> None

let as_record (r:record)
  : option T.record
  = match as_value (snd r) with
    | None -> None
    | Some v ->
      Some T.({ record_key = as_key (fst r);
                record_value = v })

let as_stamped_record (e:ms_hashfn_dom)
  : option T.stamped_record
  = let r = as_record e.r in
    if Some? r
    && e.t.e < pow2 32
    && e.t.c < pow2 32
    && e.i < pow2 16
    then (
      let t = U64.uint_to_t e.t.e in
      let c = U64.uint_to_t e.t.c in
      let i = FStar.UInt16.uint_to_t e.i in
      let ts = U64.logxor (U64.shift_left t 32ul) c in
      Some T.({
             sr_record = Some?.v r;
             sr_timestamp = ts;
             sr_thread_id = i
             })
    )
    else None

let as_ms_hash_value h = lseq_u8_to_bv h
let as_u8_hash_value h = bv_to_lseq_u8 h

let hash_entry (e: ms_hashfn_dom)
  : HA.hash_value_t
  = match as_stamped_record e with
    | None ->
      unspecified_hash_function e
    | Some r ->
      let b = serializer r in
      HA.hash_value b

(*
 * incremental multiset hash function - update the
 * hash given a new element
 *)
let ms_hashfn_upd (e: ms_hashfn_dom) (h: ms_hash_value)
  : Tot ms_hash_value
  = as_ms_hash_value (
        HA.aggregate_hash_value (as_u8_hash_value h)
                                (hash_entry e)
    )

let lemma_mshashfn_correct (s1 s2: seq ms_hashfn_dom)
  : Lemma (requires (seq2mset #_ #ms_hashfn_dom_cmp s1 ==
                     seq2mset #_ #ms_hashfn_dom_cmp s2))
          (ensures (ms_hashfn s1 = ms_hashfn s2))
  = introduce forall x. Seq.count x s1 == Seq.count x s2
    with (seq2mset_mem #_ #ms_hashfn_dom_cmp s1 x;
          seq2mset_mem #_ #ms_hashfn_dom_cmp s2 x);
    length_size #_ #ms_hashfn_dom_cmp s1;
    length_size #_ #ms_hashfn_dom_cmp s2;
    assert (Seq.length s1 == Seq.length s2);
    admit()

(* aggregation of multiset hashes *)
let ms_hashfn_agg (h1: ms_hash_value) (h2: ms_hash_value)
  : Tot ms_hash_value
  = as_ms_hash_value (
       HA.aggregate_hash_value
         (as_u8_hash_value h1)
         (as_u8_hash_value h2)
    )

// let ms_hashfn_agg_empty (h:ms_hash_value)
//   : Lemma (ensures ms_hashfn_agg empty_hash_value h == h)
//           [SMTPat (ms_hashfn_agg empty_hash_value h)]
//   = admit()

// let ms_hashfn_agg_sym (h0 h1:ms_hash_value)
//   : Lemma (ensures ms_hashfn_agg h0 h1 ==
//                    ms_hashfn_agg h1 h0)
//            [SMTPat (ms_hashfn_agg h0 h1)]
//   = admit()

// let ms_hashfn_agg_assoc (h0 h1 h2:ms_hash_value)
//   : Lemma (ensures ms_hashfn_agg h0 (ms_hashfn_agg h1 h2) ==
//                    ms_hashfn_agg (ms_hashfn_agg h0 h1) h2)
//            [SMTPat (ms_hashfn_agg h0 (ms_hashfn_agg h1 h2))]
//   = admit()

let agg_empty (h:u8_hash_value)
  : Lemma (ensures HA.aggregate_hash_value (as_u8_hash_value empty_hash_value) h == h)
          [SMTPat (HA.aggregate_hash_value (as_u8_hash_value empty_hash_value) h)]
  = admit()

let agg_sym (h0 h1:u8_hash_value)
  : Lemma (ensures HA.aggregate_hash_value h0 h1 ==
                   HA.aggregate_hash_value h1 h0)
           [SMTPat (HA.aggregate_hash_value h0 h1)]
  = admit()

let agg_assoc (h0 h1 h2:u8_hash_value)
  : Lemma (ensures HA.aggregate_hash_value h0 (HA.aggregate_hash_value h1 h2) ==
                   HA.aggregate_hash_value (HA.aggregate_hash_value h0 h1) h2)
           [SMTPat (HA.aggregate_hash_value h0 (HA.aggregate_hash_value h1 h2))]
  = admit()

let inverse_hash_value_conversion1 (h:ms_hash_value)
  : Lemma (as_ms_hash_value (as_u8_hash_value h) == h)
          [SMTPat (as_ms_hash_value (as_u8_hash_value h))]
  = admit()
let inverse_hash_value_conversion2 (h:u8_hash_value)
  : Lemma (as_u8_hash_value (as_ms_hash_value h) == h)
          [SMTPat (as_u8_hash_value (as_ms_hash_value h))]
  = admit()


let rec lemma_hashfn_agg (s1 s2: seq ms_hashfn_dom)
  : Lemma
    (ensures ms_hashfn (append s1 s2) = ms_hashfn_agg (ms_hashfn s1) (ms_hashfn s2))
    (decreases (Seq.length s2))
  = reveal_opaque (`%ms_hashfn) ms_hashfn;
    if Seq.length s2 = 0
    then (
      assert (Seq.append s1 s2 `Seq.equal` s1);
      assert (ms_hashfn s2 == empty_hash_value)
    )
    else (
      let n = Seq.length s2 - 1 in
      let s2' = SeqAux.prefix s2 n in
      let last = Seq.index s2 n in
      lemma_hashfn_agg s1 s2';
      assert (Seq.equal (append s1 s2)
                        (Seq.snoc (append s1 s2') last));
      assert (Seq.equal (SeqAux.prefix (append s1 s2) (Seq.length (append s1 s2) - 1))
                        (append s1 s2'));
      assert (ms_hashfn (append s1 s2) ==
              ms_hashfn_agg (ms_hashfn (append s1 s2'))
                            (as_ms_hash_value (hash_entry last))))

let ms_hashfn_sym (s1 s2: seq ms_hashfn_dom)
  : Lemma
    (ensures ms_hashfn (append s1 s2) = ms_hashfn (append s2 s1))
  = lemma_hashfn_agg s1 s2;
    lemma_hashfn_agg s2 s1
