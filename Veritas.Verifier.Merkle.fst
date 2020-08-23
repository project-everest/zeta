module Veritas.Verifier.Merkle

open Veritas.BinTreePtr
open Veritas.Interleave


(* eac_value is either empty or points to a a descendant *)
let lemma_eac_value_empty_or_points_to_desc 
  (#p:pos) 
  (itsl: eac_ts_log p)
  (k:key{is_merkle_key k})
  (c:bin_tree_dir):
  Lemma (requires True)
        (ensures (mv_points_to_none (to_merkle_value (eac_value itsl k)) c \/ 
                  is_desc (mv_pointed_key (to_merkle_value (eac_value itsl k)) c) (child c k)))
  = admit()

let eac_ptrfn_aux (#p:pos) (itsl: eac_ts_log p) (n:bin_tree_node) (c:bin_tree_dir):
  option (d:bin_tree_node{is_desc d (child c n)}) = 
  if depth n >= key_size then None
  else
    let v = to_merkle_value (eac_value itsl n) in
    let dh = desc_hash_dir v c in
    match dh with
    | Empty -> None
    | Desc dk _ _ -> 
      lemma_eac_value_empty_or_points_to_desc itsl n c;
      Some dk

let eac_ptrfn (#p:pos) (itsl: eac_ts_log p): ptrfn =
  eac_ptrfn_aux itsl

let lemma_has_add_equiv_root_reachable 
  (#p:pos) 
  (itsl:eac_ts_log p) (k:merkle_key{k <> Root}):
  Lemma (requires (True))
        (ensures (has_some_add_of_key k (project_seq itsl) <==> root_reachable (eac_ptrfn itsl) k))
  = admit()


let proving_ancestor (#p:pos) (itsl: eac_ts_log p) (k:key{k <> Root}): 
    k':key{is_proper_desc k k'} = admit()

(* after the first add the proving ancestor always points to self *)
let lemma_proving_ancestor_points_to_self (#p:pos) (itsl: eac_ts_log p) (k:key{k <> Root}):
  Lemma (requires not (is_eac_state_init itsl k))
        (ensures (mv_points_to (to_merkle_value (eac_value itsl (proving_ancestor itsl k)))
                               (desc_dir k (proving_ancestor itsl k))
                               k)) = admit()

(* before the first add the proving ancestor points to none or to a key that is not an ancestor *)
let lemma_proving_ancestor_initial (#p:pos) (itsl: eac_ts_log p) (k:key{k <> Root}):
  Lemma (requires (is_eac_state_init itsl k))
        (ensures (mv_points_to_none (to_merkle_value (eac_value itsl (proving_ancestor itsl k)))
                                    (desc_dir k (proving_ancestor itsl k)) \/
                  not (is_desc k (mv_pointed_key (to_merkle_value (eac_value itsl (proving_ancestor itsl k)))
                                                 (desc_dir k (proving_ancestor itsl k)))))) = admit()

(* if the proving ancestor of k is not Root, then Root points to some proper ancestor of 
 * k along that direction *)
let lemma_non_proving_ancestor_root (#p:pos) (itsl: eac_ts_log p) (k:key{k <> Root}):
  Lemma (requires (Root <> proving_ancestor itsl k))
        (ensures (is_proper_desc k Root /\
                  mv_points_to_some (eac_merkle_value itsl Root)
                                    (desc_dir k Root) /\
                  is_proper_desc k (mv_pointed_key (eac_merkle_value itsl Root)
                                                   (desc_dir k Root)))) = admit()

(* version of the previous lemma for non-root keys *)
let lemma_non_proving_ancestor (#p:pos) (itsl: eac_ts_log p) (k:key{k <> Root}) (k':key{is_proper_desc k k'}):
  Lemma (requires (k' <> proving_ancestor itsl k) /\ not (is_eac_state_init itsl k))
        (ensures (mv_points_to_some (eac_merkle_value itsl k')
                                    (desc_dir k k')) /\
                 (is_proper_desc k (mv_pointed_key (eac_merkle_value itsl k')
                                                   (desc_dir k k')))) = admit()


let lemma_proving_ancestor_has_hash (#p:pos) (itsl: eac_ts_log p) (k:key{k<> Root}):
  Lemma (requires (is_eac_state_evicted_merkle itsl k))
        (ensures (mv_pointed_hash (eac_merkle_value itsl (proving_ancestor itsl k))
                                  (desc_dir k (proving_ancestor itsl k)) = 
                  hashfn (eac_value itsl k))) = admit()

(* when evicted as blum the proving ancestor contains a bit indicating the eviction *)
let lemma_proving_ancestor_blum_bit (#p:pos) (itsl: eac_ts_log p) (k:key{k <> Root}):
  Lemma (requires (is_eac_state_evicted itsl k))
        (ensures (mv_evicted_to_blum (eac_merkle_value itsl (proving_ancestor itsl k))
                                     (desc_dir k (proving_ancestor itsl k)) = 
                  is_eac_state_evicted_blum itsl k)) = admit()
      
let lemma_addm_ancestor_is_proving (#p:pos) (itsl: eac_ts_log p {length itsl > 0}):
  Lemma (requires (AddM? (its_vlog_entry itsl (length itsl - 1))))
        (ensures (Root <> vlog_entry_key (its_vlog_entry itsl (length itsl - 1)) /\        
                  AddM?.k' (its_vlog_entry itsl (length itsl - 1)) = 
                  proving_ancestor (its_prefix itsl (length itsl - 1))
                                   (vlog_entry_key (its_vlog_entry itsl (length itsl - 1))))) = admit()

 let lemma_store_contains_proving_ancestor (#p:pos) (itsl: eac_ts_log p) 
  (tid:nat{tid < p}) (k:key{k <> Root}):
  Lemma (store_contains (thread_store (verifier_thread_state itsl tid)) k ==>
         store_contains (thread_store (verifier_thread_state itsl tid)) 
                        (proving_ancestor itsl k)) = admit()
