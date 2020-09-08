module Veritas.Verifier.Merkle

open FStar.Seq
open Veritas.BinTree
open Veritas.Hash
open Veritas.Key
open Veritas.Record
open Veritas.SeqAux
open Veritas.Verifier
open Veritas.Verifier.TSLog

module I = Veritas.Interleave
module V = Veritas.Verifier
module TL = Veritas.Verifier.TSLog

let mv_points_to_none (v: merkle_value) (d:bin_tree_dir): bool = 
  desc_hash_dir v d = Empty

let mv_points_to_some (v:merkle_value) (d:bin_tree_dir): bool = 
  Desc? (desc_hash_dir v d) 

let mv_pointed_key (v:merkle_value) (d:bin_tree_dir{mv_points_to_some v d}): key = 
  Desc?.k (desc_hash_dir v d)

let mv_pointed_hash (v:merkle_value) (d:bin_tree_dir{mv_points_to_some v d}): hash_value = 
  Desc?.h (desc_hash_dir v d)

let mv_points_to (v:merkle_value) (d:bin_tree_dir) (k:key): bool = 
  mv_points_to_some v d && mv_pointed_key v d = k

let mv_evicted_to_blum (v:merkle_value) (d:bin_tree_dir {mv_points_to_some v d}): bool =
  Desc?.b (desc_hash_dir v d)

let eac_merkle_value (itsl: TL.eac_log) (k:merkle_key): merkle_value =
  to_merkle_value (eac_value itsl k)

(* the ancestor who holds the proof of the value of key k *)
val proving_ancestor (itsl: TL.eac_log) (k:key{k <> Root}):
  k':key{is_proper_desc k k'}

(* after the first add the proving ancestor always points to self *)
val lemma_proving_ancestor_points_to_self (itsl: TL.eac_log) (k:key{k <> Root}):
  Lemma (requires not (is_eac_state_init itsl k))
        (ensures (mv_points_to (eac_merkle_value itsl (proving_ancestor itsl k))
                               (desc_dir k (proving_ancestor itsl k))
                               k))
        [SMTPat (proving_ancestor itsl k)]

(* before the first add the proving ancestor points to none or to a key that is not an ancestor *)
val lemma_proving_ancestor_initial (itsl: TL.eac_log) (k:key{k <> Root}):
  Lemma (requires (is_eac_state_init itsl k))
        (ensures (mv_points_to_none (eac_merkle_value itsl (proving_ancestor itsl k))
                                    (desc_dir k (proving_ancestor itsl k)) \/
                  not (is_desc k (mv_pointed_key (eac_merkle_value itsl (proving_ancestor itsl k))
                                                 (desc_dir k (proving_ancestor itsl k))))))

(* if the proving ancestor of k is not Root, then Root points to some proper ancestor of 
 * k along that direction *)
val lemma_non_proving_ancestor_root (itsl: TL.eac_log) (k:key{k <> Root}):
  Lemma (requires (Root <> proving_ancestor itsl k))
        (ensures (is_proper_desc k Root /\
                  mv_points_to_some (eac_merkle_value itsl Root)
                                    (desc_dir k Root) /\
                  is_proper_desc k (mv_pointed_key (eac_merkle_value itsl Root)
                                                   (desc_dir k Root))))

(* version of the previous lemma for non-root keys *)
val lemma_non_proving_ancestor (itsl: TL.eac_log) (k:key{k <> Root}) (k':key{is_proper_desc k k'}):
  Lemma (requires (k' <> proving_ancestor itsl k) /\ not (is_eac_state_init itsl k))
        (ensures (mv_points_to_some (eac_merkle_value itsl k')
                                    (desc_dir k k')) /\
                 (is_proper_desc k (mv_pointed_key (eac_merkle_value itsl k')
                                                   (desc_dir k k'))))

(* when evicted as merkle the proving ancestor contains our hash *)
val lemma_proving_ancestor_has_hash (itsl: TL.eac_log) (k:key{k<> Root}):
  Lemma (requires (is_eac_state_evicted_merkle itsl k))
        (ensures (mv_pointed_hash (eac_merkle_value itsl (proving_ancestor itsl k))
                                  (desc_dir k (proving_ancestor itsl k)) = 
                  hashfn (eac_value itsl k)))

(* when evicted as blum the proving ancestor contains a bit indicating the eviction *)
val lemma_proving_ancestor_blum_bit (itsl: TL.eac_log) (k:key{k <> Root}):
  Lemma (requires (is_eac_state_evicted itsl k))
        (ensures (mv_evicted_to_blum (eac_merkle_value itsl (proving_ancestor itsl k))
                                     (desc_dir k (proving_ancestor itsl k)) = 
                  is_eac_state_evicted_blum itsl k))
      
val lemma_addm_ancestor_is_proving (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (TL.is_eac (I.prefix itsl (I.length itsl - 1)) /\
                   AddM? (I.index itsl (I.length itsl - 1))))
        (ensures (Root <> V.key_of (I.index itsl (I.length itsl - 1)) /\        
                  AddM?.k' (I.index itsl (I.length itsl - 1)) = 
                  proving_ancestor (I.prefix itsl (I.length itsl - 1))
                                   (V.key_of (I.index itsl (I.length itsl - 1)))))

(* if the store contains a k, it contains its proving ancestor *)
val lemma_store_contains_proving_ancestor (itsl: TL.eac_log) 
  (tid:TL.valid_tid itsl) (k:key{k <> Root}):
  Lemma (store_contains (TL.thread_store itsl tid) k ==>
         store_contains (TL.thread_store itsl tid)
                        (proving_ancestor itsl k))


