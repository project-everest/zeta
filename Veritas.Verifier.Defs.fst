module Veritas.Verifier.Defs

let hashfn (m:merkle_payload): hash_value = admit()

let empty_hash_value = zero_vec 

let ms_hashfn_upd (e:ms_hashfn_dom) (h:ms_hash_value): ms_hash_value = admit()

let lemma_mshashfn_correct (s1 s2: seq ms_hashfn_dom):
  Lemma (requires (seq2mset s1 == seq2mset s2))
        (ensures (ms_hashfn s1 = ms_hashfn s2)) = admit()
