module Zeta.High.Merkle

open Zeta.App
open Zeta.BinTreePtr
open Zeta.Interleave
open Zeta.Merkle

module HV = Zeta.High.Verifier
module BP=Zeta.BinTreePtr
module M=Zeta.Merkle

(* does the log entry update which descendant the value of k points to? *)
let updates_points_to (#app:_) (e: vlog_entry app) (k: merkle_key): bool =
  match e with
  | AddM r k1 k2 -> k1 = k || k2 = k
  | _ -> false

let is_keyed (#app:_) (e: vlog_entry app)
  = match e with
    | AddM _ _ _
    | AddB _ _ _ _
    | EvictM _ _
    | EvictB _ _
    | EvictBM _ _ _ -> true
    | _ -> false

let key_of (#app:_) (e: vlog_entry app {is_keyed e})
  = match e with
    | AddM _ k _ -> k
    | AddB _ k _ _ -> k
    | EvictM k _ -> k
    | EvictB k _ -> k
    | EvictBM k _ _ -> k

let ptrfn_aux (#app #n:_) (il: eac_log app n) (k:merkle_key) (c:bin_tree_dir)
  : option (base_key)
  = let v = eac_value k il in
    if M.points_to_none c v
    then None
    else Some (M.pointed_key v c)

let lemma_eac_value_is_stored_value
  (#app #n:_)
  (il: eac_log app n)
  (k:merkle_key)
  (tid:nat{tid < n})
  : Lemma (requires (store_contains (thread_store tid il) k))
          (ensures (EACInStore? (eac_state_of_key k il) /\
                    HI.eac_value (IntK k) il = HV.stored_value (thread_store tid il) k))
  = eac_value_is_stored_value il (IntK k) tid

let init_value = {left = Empty; right = Empty}

let eac_value_init
  (#app #n:_)
  (k: merkle_key)
  (il: eac_log app n)
  : Lemma (ensures (let es = eac_state_of_key k il in
                    es = EACInit ==> eac_value k il = init_value))
          [SMTPat (eac_value k il)]
  = admit()

(*
let eac_value_unchanged_addb
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (k: merkle_key)
  : Lemma (requires (let i = length il - 1 in
                     let e = index il i in
                     AddB? e))
          (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    eac_value k il = eac_value k il'))
          [SMTPat (eac_value k il)]
  = let i = length il - 1 in
    let il' = prefix il i in
    let e = index il i in
    let es' = eac_state_of_key k il' in
    let es = eac_state_of_key k il in
    eac_state_snoc k il;

    if e `refs_key` k then
      admit()
    else (
      assert(es' = es);
      match es' with
      | EACInit -> ()
      | EACInStore _ _ _ ->
        admit()
      | _ -> admit()
    )
let points_to_unchanged_addb
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (k: merkle_key)
  (c:bin_tree_dir)
  : Lemma (requires (let i = length il - 1 in
                     let e = index il i in
                     AddB? e))
          (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    ptrfn_aux il k c = ptrfn_aux il' k c))
  = eac_value_unchanged_addb il k
*)

(* the ancestor who holds the proof of the value of key k *)
let proving_ancestor (#app #n:_) (il: eac_log app n) (k:base_key{k <> Root}):
  k':base_key{is_proper_desc k k'}
  = admit()

(* after the first add the proving ancestor always points to self *)
let lemma_proving_ancestor_points_to_self (#app #n:_) (il: eac_log app n) (k:base_key{k <> Root}):
  Lemma (requires (eac_state_of_key k il <> EACInit))
        (ensures (let pk = proving_ancestor il k in
                  let d = desc_dir k pk in
                  let v = eac_value pk il in
                  points_to v d k))
  = admit()

(* before the first add the proving ancestor points to none or to a key that is not an ancestor *)
let lemma_proving_ancestor_initial (#app #n:_) (il: eac_log app n) (k:base_key{k <> Root}):
  Lemma (requires (eac_state_of_key k il = EACInit))
        (ensures (let k' = proving_ancestor il k in
                  let v' = eac_value k' il in
                  let c = desc_dir k k' in
                  points_to_none c v' \/
                  not (is_desc k (pointed_key v' c))))
  = admit()

(* when evicted as merkle the proving ancestor contains our hash *)
let lemma_proving_ancestor_has_hash (#app #n:_) (il: eac_log app n) (gk:key app{gk <> IntK Root}):
  Lemma (requires (let k = to_base_key gk in
                   EACEvictedMerkle? (eac_state_of_key k il)))
        (ensures (let k = to_base_key gk in
                  let pk = proving_ancestor il k in
                  let mv = eac_value pk il in
                  let c = desc_dir k pk in
                  let v = HI.eac_value gk il in
                  pointed_hash mv c = hashfn v))
  = admit()

let lemma_addm_ancestor_is_proving (#app #n:_) (il: verifiable_log app n {length il > 0}):
  Lemma (requires (let n = length il in
                   let il' = I.prefix il (n-1) in
                   let e = I.index il (n-1) in
                   is_eac il' /\ AddM? e))
        (ensures (let n = length il in
                  let e = I.index il (n - 1) in
                  let il' = I.prefix il (n - 1) in
                  let AddM _ k k' = e in
                  Root <> k /\ k' = proving_ancestor il' k))
  = admit()


(* when evicted as blum the proving ancestor contains a bit indicating the eviction *)
let lemma_proving_ancestor_blum_bit (#app #n:_) (il: eac_log app n) (k:base_key{k <> Root}):
  Lemma (ensures (proving_ancestor_has_blum_bit il k))
  = admit()

(* if the store contains a k, it contains its proving ancestor *)
let lemma_store_contains_proving_ancestor (#app #n:_) (il: eac_log app n) (tid:nat{tid < n}) (k:base_key{k <> Root}):
  Lemma (requires (let es = eac_state_of_key k il in
                   EACInStore? es /\
                   EACInStore?.m es = MAdd))
        (ensures (let pk = proving_ancestor il k in
                  let st = thread_store tid il in
                  store_contains st k ==> store_contains st pk))
  = admit()

(* if a key pk points to key k, then pk is the proving ancestor of k; (inverse of
 * lemma_proving_ancestor_points_to_self *)
let lemma_points_to_implies_proving_ancestor
  (#app #n:_)
  (il: eac_log app n)
  (k:base_key)
  (k':merkle_key)
  (d:bin_tree_dir):
  Lemma (requires (let mv = eac_value k' il in
                   points_to mv d k))
        (ensures (k <> Root /\ proving_ancestor il k = k'))
  = admit()

(* precond: k' is a proper ancestor of k, but not the proving ancestor.
 *          k' is also initialized (previously added)
 * ensures: k' points to something along direction (k' -> k) and that something is an ancestor of pk
 *)
let lemma_init_ancestor_ancestor_of_proving
  (#app #n:_)
  (il: eac_log app n)
  (k:base_key)
  (k':base_key{is_proper_desc k k'}):
  Lemma (requires ((k' = Root \/ eac_state_of_key k' il <> EACInit) /\
                    k' <> proving_ancestor il k))
        (ensures (let d = desc_dir k k' in
                  let mv = eac_value k' il in
                  let pk = proving_ancestor il k in
                  points_to_some mv d /\
                  is_desc pk (pointed_key mv d)))
  = admit()

(* if a merkle value of key k points to a key kd in some direction d, then kd is a proper desc of
 * k in direction d *)
let lemma_points_to_dir_correct (#app #n:_) (il: eac_log app n) (k:merkle_key) (d:bin_tree_dir):
  Lemma (requires (let mv = eac_value k il in
                   points_to_some mv d))
        (ensures (let mv = eac_value k il in
                  let kd = pointed_key mv d in
                  is_proper_desc kd k /\
                  d = desc_dir kd k))
  = admit()
