module Veritas.BinTreePtr

open Veritas.BinTree

(* 
 * ptrfn is a function that maps each node and a direction (left | right) to an 
 * optional descendant in the corresponing (left|right) subtree
 *)
type ptrfn = (n:bin_tree_node) -> (c:bin_tree_dir) -> option (d:bin_tree_node{is_desc d (child c n)})

(* Is d descendant of a following pf pointers *)
val is_pdesc (pf: ptrfn) (d a: bin_tree_node): Tot bool

(* are a1 a2 in anc-desc relationship wrt p *)
let is_panc_pdesc_sym (pf: ptrfn) (a1 a2: bin_tree_node): bool = 
  is_pdesc pf a1 a2 || is_pdesc pf a2 a1

(* unrelated in terms of p-anc-desc *)
let non_panc_pdesc (pf: ptrfn) (a1 a2: bin_tree_node): bool = 
  not (is_panc_pdesc_sym pf a1 a2)

(* every node is a pdesc of itself *)
val lemma_pdesc_reflexive (pf: ptrfn) (a: bin_tree_node):
  Lemma (is_pdesc pf a a)

(* pdesc is a transitive relation *)
val lemma_pdesc_transitive (pf: ptrfn) (a b c: bin_tree_node):
  Lemma (requires (is_pdesc pf a b /\ is_pdesc pf b c))
        (ensures (is_pdesc pf a c))

(* pointer based descendant relation *)
noeq type pdesc: ptrfn -> bin_tree_node -> bin_tree_node -> Type = 
  | PSelf: pf: ptrfn -> n:bin_tree_node -> pdesc pf n n
  | PTran: pf: ptrfn -> d:bin_tree_node -> a:bin_tree_node -> _:(pdesc pf d a) -> 
           c:bin_tree_dir{Some? (pf d c)} ->
           pdesc pf (Some?.v (pf d c)) a

