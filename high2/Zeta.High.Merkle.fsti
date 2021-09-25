module Zeta.High.Merkle

open FStar.Seq
open Zeta.SeqAux
open Zeta.BinTree
open Zeta.BinTreePtr
open Zeta.Interleave
open Zeta.Key
open Zeta.App
open Zeta.HashFunction
open Zeta.GenKey
open Zeta.Record
open Zeta.Merkle
open Zeta.EAC
open Zeta.GenericVerifier
open Zeta.Generic.Interleave
open Zeta.High.Verifier
open Zeta.High.Interleave

module I = Zeta.Interleave
module HI = Zeta.High.Interleave

let eac_merkle_value (#app #n:_) (k:merkle_key) (il: eac_log app n)
  : value
  = let gk = IntK k in
    let v = eac_value gk il in
    IntV?.v v

(* the ancestor who holds the proof of the value of key k *)
val proving_ancestor (#app #n:_) (il: eac_log app n) (k:base_key{k <> Root}):
  k':base_key{is_proper_desc k k'}

(* after the first add the proving ancestor always points to self *)
val lemma_proving_ancestor_points_to_self (#app #n:_) (il: eac_log app n) (k:base_key{k <> Root}):
  Lemma (requires (eac_state_of_key k il <> EACInit))
        (ensures (let pk = proving_ancestor il k in
                  let d = desc_dir k pk in
                  let v = eac_merkle_value pk il in
                  points_to v d k))
        [SMTPat (proving_ancestor il k)]

(* before the first add the proving ancestor points to none or to a key that is not an ancestor *)
val lemma_proving_ancestor_initial (#app #n:_) (il: eac_log app n) (k:base_key{k <> Root}):
  Lemma (requires (eac_state_of_key k il = EACInit))
        (ensures (let k' = proving_ancestor il k in
                  let v' = eac_merkle_value k' il in
                  let c = desc_dir k k' in
                  points_to_none v' c \/
                  not (is_desc k (pointed_key v' c))))

(* if a key pk points to key k, then pk is the proving ancestor of k; (inverse of
 * lemma_proving_ancestor_points_to_self *)
val lemma_points_to_implies_proving_ancestor
  (#app #n:_)
  (il: eac_log app n)
  (k:base_key)
  (k':merkle_key)
  (d:bin_tree_dir):
  Lemma (requires (let mv = eac_merkle_value k' il in
                   points_to mv d k))
        (ensures (k <> Root /\ proving_ancestor il k = k'))

(* when evicted as merkle the proving ancestor contains our hash *)
val lemma_proving_ancestor_has_hash (#app #n:_) (il: eac_log app n) (gk:key app{gk <> IntK Root}):
  Lemma (requires (let k = to_base_key gk in
                   EACEvictedMerkle? (eac_state_of_key k il) /\
                   EACEvictedMerkle?.gk (eac_state_of_key k il) = gk))
        (ensures (let k = to_base_key gk in
                  let pk = proving_ancestor il k in
                  let mv = eac_merkle_value pk il in
                  let c = desc_dir k pk in
                  let v = HI.eac_value gk il in
                  pointed_hash mv c = hashfn v))

val lemma_addm_ancestor_is_proving (#app:_) (#n:pos) (il: verifiable_log app n {length il > 0}):
  Lemma (requires (let n = length il in
                   let il' = I.prefix il (n-1) in
                   let e = I.index il (n-1) in
                   is_eac il' /\ AddM? e))
        (ensures (let n = length il in
                  let e = I.index il (n - 1) in
                  let il' = I.prefix il (n - 1) in
                  let AddM _ k k' = e in
                  Root <> k /\ k' = proving_ancestor il' k))

let is_in_blum (#app #k:_) (es: eac_state  app k): bool =
  EACEvictedBlum? es ||
  (EACInStore? es && EACInStore?.m es = BAdd)

let proving_ancestor_has_blum_bit (#app #n:_) (il: eac_log app n) (k:base_key {k <> Root})
  : bool
  = let es = eac_state_of_key k il in
    let pk = proving_ancestor il k in
    let c = desc_dir k pk in
    let mv = eac_merkle_value pk il in

    es = EACInit ||
    evicted_to_blum mv c = is_in_blum es

(* when evicted as blum the proving ancestor contains a bit indicating the eviction *)
val lemma_proving_ancestor_blum_bit (#app #n:_) (il: eac_log app n) (k:base_key{k <> Root}):
  Lemma (ensures (proving_ancestor_has_blum_bit il k))

(* if the store contains a k, it contains its proving ancestor *)
val lemma_store_contains_proving_ancestor (#app #n:_) (il: eac_log app n) (tid:nat{tid < n}) (k:base_key{k <> Root}):
  Lemma (requires (let es = eac_state_of_key k il in
                   EACInStore? es /\
                   EACInStore?.m es = MAdd))
        (ensures (let pk = proving_ancestor il k in
                  let st = thread_store tid il in
                  store_contains st k ==> store_contains st pk))

val eac_value_snoc_appkey
  (#app #n:_)
  (gkf: key app {AppK? gkf})
  (il: eac_log app n {length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let e = index il i in
                    let bkf = to_base_key gkf in
                    match e with
                    | RunApp _ _ _ -> if e `refs_key` bkf then
                                        True
                                      else
                                       eac_value gkf il = eac_value gkf il'
                    | _ -> eac_value gkf il = eac_value gkf il'))
