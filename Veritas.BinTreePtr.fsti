module Veritas.BinTreePtr

open Veritas.BinTree

(* 
 * ptrfn is a function that maps each node and a direction (left | right) to an 
 * optional descendant in the corresponing (left|right) subtree
 *)
type ptrfn = (n:bin_tree_node) -> (c:bin_tree_dir) -> option (d:bin_tree_node{is_desc d (child c n)})

(* does n point to some node along direction c *)
let points_to_some (pf:ptrfn) (n:bin_tree_node) (c:bin_tree_dir): bool = 
  Some? (pf n c)

(* if n points to n' along c, return n' *)
let pointed_node (pf:ptrfn) (n:bin_tree_node) (c:bin_tree_dir {points_to_some pf n c}): bin_tree_node = 
  Some?.v (pf n c)

(* does a point to d *)
let points_to (pf: ptrfn) (d: bin_tree_node) (a: bin_tree_node{is_proper_desc d a}): bool = 
  let c = desc_dir d a in
  points_to_some pf a c && 
  d = pointed_node pf a c 

let points_to_none (pf:ptrfn) (n:bin_tree_node): bool = 
  not (points_to_some pf n Left) && 
  not (points_to_some pf n Right)

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

(* Extend the pointer function with a new points_to edge *)
let extend_ptrfn 
  (pf:ptrfn) 
  (d:bin_tree_node{points_to_none pf d}) 
  (a:bin_tree_node{is_proper_desc d a /\
                   not (points_to_some pf a (desc_dir d a)) /\
                   root_reachable pf a}): ptrfn = 
  let c = desc_dir d a in
  fun n' c' -> if n' = a && c' = c then Some d else pf n' c'

(* extension does not reduce reachability *)
val lemma_extend_reachable 
  (pf:ptrfn) 
  (d:bin_tree_node{points_to_none pf d}) 
  (a:bin_tree_node{is_proper_desc d a /\ 
                   not (points_to_some pf a (desc_dir d a)) /\
                   root_reachable pf a})
  (n: bin_tree_node):
  Lemma (requires (root_reachable pf n))
        (ensures (root_reachable (extend_ptrfn pf d a) n))

(* extension adds reachability to the new node *)
val lemma_extend_reachable_new
  (pf:ptrfn) 
  (d:bin_tree_node{points_to_none pf d}) 
  (a:bin_tree_node{is_proper_desc d a /\ 
                   not (points_to_some pf a (desc_dir d a)) /\
                   root_reachable pf a}):
  Lemma (root_reachable (extend_ptrfn pf d a) d)
  
(* extends confers reachability only to the new node *)
val lemma_extend_not_reachable
  (pf:ptrfn) 
  (d:bin_tree_node{points_to_none pf d}) 
  (a:bin_tree_node{is_proper_desc d a /\ 
                   not (points_to_some pf a (desc_dir d a)) /\
                   root_reachable pf a})
  (n: bin_tree_node):
  Lemma (requires (not (root_reachable pf n) /\ n <> d))
        (ensures (not (root_reachable (extend_ptrfn pf d a) n)))

(* Extend the pointer function by cutting a pointer *)
let extendcut_ptrfn 
  (pf:ptrfn)
  (d:bin_tree_node{points_to_none pf d})
  (a:bin_tree_node{is_proper_desc d a /\ 
                   points_to_some pf a (desc_dir d a) /\
                   is_proper_desc (pointed_node pf a (desc_dir d a)) d /\
                   root_reachable pf a}): ptrfn = 
   let c1 = desc_dir d a in
   let d' = pointed_node pf a c1 in
   let c2 = desc_dir d' d in
   fun n' c' -> if n' = a && c' = c1 then Some d 
              else if n' = d && c' = c2 then Some d' 
              else pf n' c'

(* Root reachability is preserved with extendcut *)
val lemma_extendcut_reachable 
  (pf:ptrfn)
  (d:bin_tree_node{points_to_none pf d})
  (a:bin_tree_node{is_proper_desc d a /\ 
                    points_to_some pf a (desc_dir d a) /\
                    is_proper_desc (pointed_node pf a (desc_dir d a)) d /\ 
                    root_reachable pf a})
  (n: bin_tree_node):
  Lemma (requires (root_reachable pf n))
        (ensures (root_reachable (extendcut_ptrfn pf d a) n))

(* Root reachability is preserved with extendcut *)
val lemma_extendcut_reachable_new
  (pf:ptrfn)
  (d:bin_tree_node{points_to_none pf d})
  (a:bin_tree_node{is_proper_desc d a /\ 
                    points_to_some pf a (desc_dir d a) /\
                    is_proper_desc (pointed_node pf a (desc_dir d a)) d /\ 
                    root_reachable pf a}):
  Lemma (root_reachable (extendcut_ptrfn pf d a) d)

val lemma_extendcut_not_reachable 
  (pf:ptrfn)
  (d:bin_tree_node{points_to_none pf d})
  (a:bin_tree_node{is_proper_desc d a /\ 
                    points_to_some pf a (desc_dir d a) /\
                    is_proper_desc (pointed_node pf a (desc_dir d a)) d /\ 
                    root_reachable pf a})
  (n: bin_tree_node):
  Lemma (requires (not (root_reachable pf n) /\ n <> d))
        (ensures (not (root_reachable (extendcut_ptrfn pf d a) n)))

(* Two pointer functions are equal on all inputs *)
let feq_ptrfn (pf1: ptrfn) (pf2: ptrfn) = 
  forall n. forall c. {:pattern (pf1 n c) \/ (pf2 n c)} pf1 n c == pf2 n c

(* Two equal pointer functions have the same reachability relationship *)
val lemma_reachable_feq (pf1: ptrfn) (pf2: ptrfn) (d: bin_tree_node) (a: bin_tree_node):
  Lemma (requires (feq_ptrfn pf1 pf2))
        (ensures (reachable pf1 d a = reachable pf2 d a))
        [SMTPat (reachable pf1 d a); SMTPat (reachable pf2 d a)]

val lemma_desc_of_prev_not_reachable (pf:ptrfn)
                                     (d1:bin_tree_node)
                                     (a:bin_tree_node)
                                     (d2:bin_tree_node):
  Lemma (requires (reachable pf d1 a /\ d1 <> a /\
                   is_proper_desc d1 d2 /\
                   is_proper_desc d2 (prev_in_path pf d1 a)))
        (ensures (not (reachable pf d2 a)))

val lemma_prev_in_path_feq (pf1: ptrfn) 
                           (pf2: ptrfn) 
                           (d:bin_tree_node) 
                           (a:bin_tree_node):
   Lemma (requires (feq_ptrfn pf1 pf2 /\ reachable pf1 d a /\ d <> a))
         (ensures (prev_in_path pf1 d a = prev_in_path pf2 d a))

