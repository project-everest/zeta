module Veritas.Verifier.Merkle

open FStar.Seq
open Veritas.BinTree
open Veritas.EAC
open Veritas.Hash
open Veritas.Key
open Veritas.Record
open Veritas.SeqAux
open Veritas.Verifier
open Veritas.Verifier.TSLog

module E=Veritas.EAC
module I = Veritas.Interleave
module V = Veritas.Verifier
module TL = Veritas.Verifier.TSLog

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
        (ensures (let k' = proving_ancestor itsl k in
                  let v' = eac_merkle_value itsl k' in
                  let c = desc_dir k k' in
                  mv_points_to_none v' c \/
                  not (is_desc k (mv_pointed_key v' c))))

(* when evicted as merkle the proving ancestor contains our hash *)
val lemma_proving_ancestor_has_hash (itsl: TL.eac_log) (k:key{k<> Root}):
  Lemma (requires (is_eac_state_evicted_merkle itsl k))
        (ensures (mv_pointed_hash (eac_merkle_value itsl (proving_ancestor itsl k))
                                  (desc_dir k (proving_ancestor itsl k)) = 
                  hashfn (eac_value itsl k)))
      
val lemma_addm_ancestor_is_proving (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (TL.is_eac (I.prefix itsl (I.length itsl - 1)) /\
                   AddM? (I.index itsl (I.length itsl - 1))))
        (ensures (let n = I.length itsl in
                  let e = I.index itsl (n - 1) in
                  let itsl' = I.prefix itsl (n - 1) in
                  let k = V.key_of e in
                  Root <> k /\ AddM?.k' e = proving_ancestor itsl' k))

let is_in_blum (es: E.eac_state): bool = 
  EACEvictedBlum? es || 
  (EACInStore? es && EACInStore?.m es = BAdd)

let proving_ancestor_has_blum_bit (itsl: TL.eac_log) (k:key {k <> Root}): bool = 
  let es = TL.eac_state_of_key itsl k in
  not (E.is_eac_state_active es) || 
  mv_evicted_to_blum (eac_merkle_value itsl (proving_ancestor itsl k))
                                     (desc_dir k (proving_ancestor itsl k)) =
                      is_in_blum es

(* when evicted as blum the proving ancestor contains a bit indicating the eviction *)
val lemma_proving_ancestor_blum_bit (itsl: TL.eac_log) (k:key{k <> Root}):
  Lemma (ensures (proving_ancestor_has_blum_bit itsl k))

(* if the store contains a k, it contains its proving ancestor *)
val lemma_store_contains_proving_ancestor (itsl: TL.eac_log) 
  (tid:TL.valid_tid itsl) (k:key{k <> Root}):
  Lemma (requires (let es = TL.eac_state_of_key itsl k in
                   EACInStore? es /\
                   EACInStore?.m es = MAdd))                    
        (ensures (store_contains (TL.thread_store itsl tid) k ==>
                                 store_contains (TL.thread_store itsl tid)
                                 (proving_ancestor itsl k)))


