module Veritas.BinTreePtr

open Veritas.BinTree

(* 
 * ptrfn is a function that maps each node and a direction (left | right) to an 
 * optional descendant in the corresponing (left|right) subtree
 *)
type ptrfn = (n:bin_tree_node) -> (c:bin_tree_dir) -> option (d:bin_tree_node{is_desc d (child c n)})

let points_to (pf: ptrfn) (d: bin_tree_node) (a: bin_tree_node{is_proper_desc d a}): bool = 
  let c = desc_dir d a in
  Some? (pf a c) && d = Some?.v (pf a c) 

(* Is d reachable from a following pf pointers *)
val reachable (pf: ptrfn) (d a: bin_tree_node): Tot bool

(* is reachable from the root *)
let root_reachable (pf: ptrfn) (n: bin_tree_node): bool = reachable pf n Root

(* are a1 a2 reachable from one or the other *)
let reachable_sym (pf: ptrfn) (a1 a2: bin_tree_node): bool = 
  reachable pf a1 a2 || reachable pf a2 a1

(* unrelated in terms of p-anc-desc *)
let non_reachable_sym (pf: ptrfn) (a1 a2: bin_tree_node): bool = 
  not (reachable_sym pf a1 a2)

(* every node is a pdesc of itself *)
val lemma_reachable_reflexive (pf: ptrfn) (a: bin_tree_node):
  Lemma (reachable pf a a)

val lemma_points_to_reachable (pf: ptrfn) 
                              (d: bin_tree_node) 
                              (a: bin_tree_node):
  Lemma (requires (is_proper_desc d a /\ points_to pf d a))
        (ensures (reachable pf d a))

(* pdesc is a transitive relation *)
val lemma_reachable_transitive (pf: ptrfn) (a b c: bin_tree_node):
  Lemma (requires (reachable pf a b /\ reachable pf b c))
        (ensures (reachable pf a c))

(* previous node in the reachability path from d to a *)
val prev_in_path (pf:ptrfn) (d: bin_tree_node) (a:bin_tree_node{reachable pf d a /\ d <> a}): 
  Tot (d': bin_tree_node {is_proper_desc d d' /\ reachable pf d' a /\ points_to pf d d'})
                                    
(* 
 * if there is no c-pointer at node a, then any desc in that subtree is not 
 * reachable from a 
 *)
val lemma_non_reachable_desc_of_none (pf: ptrfn) 
                                     (d:bin_tree_node) 
                                     (a:bin_tree_node{is_proper_desc d a /\ 
                                                      None? (pf a (desc_dir d a))}):
  Lemma (not (reachable pf d a))
