module Veritas.MultiSetHash

(* Hash value of an empty set *)
let empty_hash_value: ms_hash_value = zero_vec 

let ms_hashfn_upd (e: ms_hashfn_dom) (h: ms_hash_value): Tot ms_hash_value = admit()

(* multiset hash function for a sequence *)
let rec ms_hashfn_aux (s: seq ms_hashfn_dom): Tot ms_hash_value 
  (decreases (length s)) = 
  let n = length s in
  (* empty sequence *)
  if n = 0 then empty_hash_value
  else
    let s' = prefix s (n - 1) in
    let e' = index s (n - 1) in
    let h' = ms_hashfn_aux s' in
    ms_hashfn_upd e' h'

(* multiset hash function for a sequence *)
let ms_hashfn (s: seq ms_hashfn_dom): Tot ms_hash_value = ms_hashfn_aux s

(* two sequences that encode the same multiset produce the same hash *)
let lemma_mshashfn_correct (s1 s2: seq ms_hashfn_dom):
  Lemma (requires (seq2mset s1 == seq2mset s2))
        (ensures (ms_hashfn s1 = ms_hashfn s2)) = admit()

(* aggregation of multiset hashes *)
let ms_hashfn_agg (h1: ms_hash_value) (h2: ms_hash_value) : Tot ms_hash_value = admit()

let lemma_hashfn_agg (s1 s2: seq ms_hashfn_dom):
  Lemma (ms_hashfn (append s1 s2) = ms_hashfn_agg (ms_hashfn s1) (ms_hashfn s2)) = admit()
