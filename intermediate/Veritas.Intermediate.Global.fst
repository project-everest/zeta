module Veritas.Intermediate.Global

let verifiable_implies_prefix_verifiable
  (#vcfg:_) (gl:verifiable_log vcfg) (i:nat{i <= Seq.length gl}):
  Lemma (ensures (verifiable #vcfg (SA.prefix gl i))) = 
  let pgl = SA.prefix gl i in
  let aux (tid: SA.seq_index pgl):
    Lemma (ensures (IntT.verifiable (thread_log pgl tid)))
          [SMTPat (IntT.verifiable (thread_log pgl tid))] =
    assert(thread_log pgl tid = thread_log gl tid);          
    () 
  in
  ()

let add_seq (#vcfg:_) (gl: verifiable_log vcfg): seq (ms_hashfn_dom) = admit()

let lemma_g_hadd_correct (#vcfg:_) (gl: verifiable_log vcfg):
  Lemma (ensures (hadd gl = ms_hashfn (add_seq gl))) = admit()

(* mapping from blum_add entries in verifier log to the index in add seq *)
let add_set_map (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  (j: SA.seq_index (add_seq gl){S.index (add_seq gl) j = blum_add_elem (indexss gl ii)}) = admit()

(* inverse mapping from add_seq to the blum add entries in the verifier logs *)
let add_set_map_inv (#vcfg:_) (gl: verifiable_log vcfg) (j: SA.seq_index (add_seq gl)):
  (ii: sseq_index gl {is_blum_add (indexss gl ii) /\ 
                      add_set_map gl ii = j}) = admit()
                      
let lemma_add_set_map_inv (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  Lemma (ensures (add_set_map_inv gl (add_set_map gl ii) = ii)) = admit()

(* a single sequence containing all the blum evicts *)
let evict_seq (#vcfg:_) (gl: verifiable_log vcfg): seq ms_hashfn_dom = admit()

let lemma_ghevict_correct (#vcfg:_) (gl: verifiable_log vcfg):
  Lemma (ensures (hevict gl = ms_hashfn (evict_seq gl))) = admit()

(* the global evict set is a set (not a multiset) *)
let evict_set_is_set (#vcfg:_) (gl: verifiable_log vcfg): 
  Lemma (ensures (is_set (evict_set gl))) = admit()

let evict_seq_map (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  (j: SA.seq_index (evict_seq gl) {S.index (evict_seq gl) j = 
                                 blum_evict_elem gl ii}) = admit()

let evict_seq_map_inv (#vcfg:_) (gl: verifiable_log vcfg) (j: SA.seq_index (evict_seq gl)):
  (ii: sseq_index gl {is_evict_to_blum (indexss gl ii) /\
                      blum_evict_elem gl ii = S.index (evict_seq gl) j /\
                      evict_seq_map gl ii = j}) = admit()

let lemma_evict_seq_inv (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  Lemma (requires True)
        (ensures (evict_seq_map_inv gl (evict_seq_map gl ii) = ii)) = admit()
