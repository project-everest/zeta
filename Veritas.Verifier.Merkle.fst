module Veritas.Verifier.Merkle

open FStar.Seq
open Veritas.BinTree
open Veritas.BinTreePtr

open Veritas.EAC
open Veritas.Interleave
open Veritas.Key
open Veritas.Record
open Veritas.Verifier
open Veritas.Verifier.CorrectDefs


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

