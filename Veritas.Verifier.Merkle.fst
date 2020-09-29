module Veritas.Verifier.Merkle

open Veritas.BinTreePtr
open Veritas.Interleave

module BP=Veritas.BinTreePtr

(* eac pointer function *)
let eac_ptrfn (itsl: TL.eac_log): ptrfn =
  admit()

let root_reachable (itsl: TL.eac_log) (k:key): bool = 
  let pf = eac_ptrfn itsl in
  BP.root_reachable pf k

(* a key is root reachable iff its eac_state is not EACInit *)
let lemma_not_init_equiv_root_reachable (itsl: TL.eac_log) (k:key{k <> Root}):
  Lemma (not (is_eac_state_init itsl k) <==> root_reachable itsl k) = 
  admit()

let rec first_root_reachable_ancestor (itsl: TL.eac_log) (k:key):
  Tot (k':key{root_reachable itsl k' /\
              is_desc k k'}) 
  (decreases (depth k)) = 
  let pf = eac_ptrfn itsl in
  
  if root_reachable itsl k then (
    lemma_desc_reflexive k;
    k
  )
  else (
    (* root is reachable from itself *)
    lemma_reachable_reflexive pf Root; 

    (* since k is not root_reachable, k cannot be Root *)
    assert(k <> Root);

    (* so, k has a parent *)
    let kp = parent k in

    (* recurse ... *)
    let k' = first_root_reachable_ancestor itsl kp in
    
    lemma_parent_ancestor k;
    lemma_desc_transitive k kp k';
    k'
  )

(* the ancestor who holds the proof of the value of key k *)
let proving_ancestor (itsl: TL.eac_log) (k:key{k <> Root}):
  k':key{is_proper_desc k k'} = 
  let pf = eac_ptrfn itsl in
  lemma_not_init_equiv_root_reachable itsl k;
  
  if root_reachable itsl k then 
    //assert(not (is_eac_state_init itsl k));
    prev_in_path pf k Root  
  else first_root_reachable_ancestor itsl k

(* after the first add the proving ancestor always points to self *)
let lemma_proving_ancestor_points_to_self (itsl: TL.eac_log) (k:key{k <> Root}):
  Lemma (requires not (is_eac_state_init itsl k))
        (ensures (mv_points_to (eac_merkle_value itsl (proving_ancestor itsl k))
                               (desc_dir k (proving_ancestor itsl k))
                               k)) =
  admit()                               
   

(* before the first add the proving ancestor points to none or to a key that is not an ancestor *)
let lemma_proving_ancestor_initial (itsl: TL.eac_log) (k:key{k <> Root}):
  Lemma (requires (is_eac_state_init itsl k))
        (ensures (mv_points_to_none (eac_merkle_value itsl (proving_ancestor itsl k))
                                    (desc_dir k (proving_ancestor itsl k)) \/
                  not (is_desc k (mv_pointed_key (eac_merkle_value itsl (proving_ancestor itsl k))
                                                 (desc_dir k (proving_ancestor itsl k)))))) = 
  admit()                                                 

(* if the proving ancestor of k is not Root, then Root points to some proper ancestor of 
 * k along that direction *)
let lemma_non_proving_ancestor_root (itsl: TL.eac_log) (k:key{k <> Root}):
  Lemma (requires (Root <> proving_ancestor itsl k))
        (ensures (is_proper_desc k Root /\
                  mv_points_to_some (eac_merkle_value itsl Root)
                                    (desc_dir k Root) /\
                  is_proper_desc k (mv_pointed_key (eac_merkle_value itsl Root)
                                                   (desc_dir k Root))))
  = admit()                                                   

(* version of the previous lemma for non-root keys *)
let lemma_non_proving_ancestor (itsl: TL.eac_log) (k:key{k <> Root}) (k':key{is_proper_desc k k'}):
  Lemma (requires (k' <> proving_ancestor itsl k) /\ not (is_eac_state_init itsl k))
        (ensures (mv_points_to_some (eac_merkle_value itsl k')
                                    (desc_dir k k')) /\
                 (is_proper_desc k (mv_pointed_key (eac_merkle_value itsl k')
                                                   (desc_dir k k')))) = 
  admit()                                                   

(* when evicted as merkle the proving ancestor contains our hash *)
let lemma_proving_ancestor_has_hash (itsl: TL.eac_log) (k:key{k<> Root}):
  Lemma (requires (is_eac_state_evicted_merkle itsl k))
        (ensures (mv_pointed_hash (eac_merkle_value itsl (proving_ancestor itsl k))
                                  (desc_dir k (proving_ancestor itsl k)) = 
                  hashfn (eac_value itsl k))) = 
  admit()                  

(* when evicted as blum the proving ancestor contains a bit indicating the eviction *)
let lemma_proving_ancestor_blum_bit (itsl: TL.eac_log) (k:key{k <> Root}):
  Lemma (requires (is_eac_state_evicted itsl k))
        (ensures (mv_evicted_to_blum (eac_merkle_value itsl (proving_ancestor itsl k))
                                     (desc_dir k (proving_ancestor itsl k)) = 
                  is_eac_state_evicted_blum itsl k)) = admit()
      
let lemma_addm_ancestor_is_proving (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (TL.is_eac (I.prefix itsl (I.length itsl - 1)) /\
                   AddM? (I.index itsl (I.length itsl - 1))))
        (ensures (Root <> V.key_of (I.index itsl (I.length itsl - 1)) /\        
                  AddM?.k' (I.index itsl (I.length itsl - 1)) = 
                  proving_ancestor (I.prefix itsl (I.length itsl - 1))
                                   (V.key_of (I.index itsl (I.length itsl - 1))))) = 
   admit()                                   

(* if the store contains a k, it contains its proving ancestor *)
let lemma_store_contains_proving_ancestor (itsl: TL.eac_log) 
  (tid:TL.valid_tid itsl) (k:key{k <> Root}):
  Lemma (store_contains (TL.thread_store itsl tid) k ==>
         store_contains (TL.thread_store itsl tid)
                        (proving_ancestor itsl k)) = admit()

