module Veritas.Verifier.Global

(* aggregate hadd over all verifier threads *)
let hadd (gl: verifiable_log): ms_hash_value =
  let th = fun (tl:VT.verifiable_log) -> (thread_hadd (t_verify (fst tl) (snd tl))) in
  let f = fun (tl:VT.verifiable_log) (h:ms_hash_value) -> (ms_hashfn_agg (th tl) h) in
  reduce empty_hash_value f (verifiable_threads gl)

(* aggregate hadd over all verifier threads *)
let hevict (gl: verifiable_log): ms_hash_value =
  let th = fun (tl:VT.verifiable_log) -> (thread_hevict (t_verify (fst tl) (snd tl))) in
  let f = fun (tl:VT.verifiable_log) (h:ms_hash_value) -> (ms_hashfn_agg (th tl) h) in
  reduce empty_hash_value f (verifiable_threads gl)

let clock (gl: verifiable_log) (i: sseq_index gl): timestamp = admit()

let time_seq_ctor (gl: verifiable_log): (interleave_ctor gl) = admit()
