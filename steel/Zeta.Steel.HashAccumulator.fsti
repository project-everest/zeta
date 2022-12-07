module Zeta.Steel.HashAccumulator
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module A = Steel.ST.Array
open Steel.ST.Util


inline_for_extraction noextract
let blake2_max_input_length = pow2 32 - 1 - 128

// NOTE: we do not have an agile spec for the keyed hash functionality :(, so
// we're making Blake2-dependent assumptions without corresponding agile predicates
noextract inline_for_extraction
let hashable_bytes = s:Seq.seq U8.t { Seq.length s <= blake2_max_input_length }
let hashable_buffer = b:A.array U8.t { A.length b <= blake2_max_input_length }

let key_len = 128
let key_t = Seq.lseq U8.t key_len
let key_buffer = k:A.array U8.t { A.length k == key_len }

let iv_len = 96
let iv_t = Seq.lseq U8.t iv_len
let iv_buffer = b:A.array U8.t { A.length b == iv_len }

let hash_len = 32
let hash_value_t = 
  Seq.lseq U8.t hash_len &
  nat
  
let ehash_value_t = Ghost.erased hash_value_t

val ha
  : Type0

val ha_val (r:ha) (v:ehash_value_t)
  : vprop
  
val initial_hash
  : hash_value_t

val hash_one_value (k:key_t) (iv:iv_t) (_:hashable_bytes)
  : hash_value_t

val aggregate_hashes (_ _: hash_value_t)
  : hash_value_t

val initial_hash_unit (h:hash_value_t)
  : Lemma (aggregate_hashes initial_hash h == h)

val aggregate_hashes_commutative (h1 h2:hash_value_t)
  : Lemma (aggregate_hashes h1 h2 == aggregate_hashes h2 h1)

val aggregate_hashes_associative (h1 h2 h3:hash_value_t)
  : Lemma (aggregate_hashes h1 (aggregate_hashes h2 h3) ==
           aggregate_hashes (aggregate_hashes h1 h2) h3)

(*** THE MAIN INTERFACE ***)

(** Create an instance of a hash accumulator in the heap *)
val create (_:unit)
  : STT ha
    emp
    (fun s -> ha_val s initial_hash)

(** Free the hash accumulator *)
val reclaim (#h:ehash_value_t) (s:ha)
  : STT unit
    (ha_val s h)
    (fun _ -> emp)

//TODO: can't inline this if in the ensures of aggregate
let maybe_aggregate_hashes (b:bool) (h0 h1: hash_value_t) =
  if b then aggregate_hashes h0 h1
  else h0

val aggregate (#h1 #h2:ehash_value_t) (b1 b2: ha)
  : STT bool
    (ha_val b1 h1 `star` ha_val b2 h2)
    (fun b -> ha_val b1 (maybe_aggregate_hashes b h1 h2) `star` ha_val b2 h2)

val compare (#h1 #h2:ehash_value_t) (b1 b2:ha)
  : ST bool
    (ha_val b1 h1 `star` ha_val b2 h2)
    (fun _ -> ha_val b1 h1 `star` ha_val b2 h2)
    (requires True)
    (ensures fun success ->
      success <==> (h1 == h2))
  
(** Hash the (input[0, l)) into the hash accumulate s *)
val add (#h:ehash_value_t) (ha:ha)
        (#p:perm) 
        (#kv:Ghost.erased key_t)
        (#ivv:Ghost.erased iv_t)
        (#s:Ghost.erased (Seq.seq U8.t))
        (k: key_buffer)
        (iv: iv_buffer)
        (input:hashable_buffer)
        (l:U32.t { U32.v l <= Seq.length s /\
                   A.length input == Seq.length s })
  : STT bool
        (ha_val ha h `star`
         A.pts_to k p kv `star`
         A.pts_to iv p ivv `star`         
         A.pts_to input p s)
        (fun b -> ha_val ha 
                      (maybe_aggregate_hashes b h
                        (hash_one_value kv ivv (Seq.slice s 0 (U32.v l)))) `star`
               A.pts_to k p kv `star`
               A.pts_to iv p ivv `star`         
               A.pts_to input p s)
           
