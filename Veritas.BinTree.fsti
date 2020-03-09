module Veritas.BinTree

open FStar.BitVector

(* Nodes in an infinite binary tree *)
type bin_tree_node = 
  | Root: bin_tree_node 
  | LeftChild: n:bin_tree_node -> bin_tree_node
  | RightChild: n:bin_tree_node -> bin_tree_node

(* non-root binary tree node *)
type non_root_node = (n:bin_tree_node{~(Root? n)})

(* Depth of a binary tree node *)
let rec depth (n:bin_tree_node): Tot nat = 
  match n with 
  | Root -> 0
  | LeftChild n' -> 1 + depth n'
  | RightChild n' -> 1 + depth n'

(* Parent of a node *)
let parent (n:non_root_node): Tot bin_tree_node = 
  match n with
  | LeftChild n' -> n'
  | RightChild n' -> n'

(* Possible child node direction *)
type bin_tree_dir = 
  | Left
  | Right

let other_dir (c:bin_tree_dir): bin_tree_dir = 
  match c with
  | Left -> Right
  | Right -> Left

(* Child node with a specified direction (left|right) *)
let child (d:bin_tree_dir) (n:bin_tree_node) = 
  match d with
  | Left -> LeftChild n
  | Right -> RightChild n

let sibling (n:non_root_node): Tot bin_tree_node = 
  match n with
  | LeftChild p -> RightChild p
  | RightChild p -> LeftChild p

(* Is d descendant of a *)
val is_desc (d a: bin_tree_node): Tot bool

(* in an ancestor-desc relationship *)
let is_anc_desc_sym (a1 a2: bin_tree_node): bool = 
  is_desc a1 a2 || is_desc a2 a1

(* unrelated in terms of ancestor-desc *)
let non_anc_desc (a1 a2: bin_tree_node): bool = 
  not (is_anc_desc_sym a1 a2)

(* Every node is a descendant of root *)
val lemma_root_is_univ_ancestor (a: bin_tree_node):
  Lemma (is_desc a Root)

(* Every node is a descendant of itself *)
val lemma_desc_reflexive (a: bin_tree_node):
  Lemma (is_desc a a)

(* descendant is a transitive relation *)
val lemma_desc_transitive (a b c: bin_tree_node):
  Lemma (is_desc a b /\ is_desc b c ==> is_desc a c)

(* descendant depth >= ancestor depth *)
val lemma_desc_depth_monotonic (d a: bin_tree_node):
  Lemma (requires (is_desc d a))
        (ensures (depth d >= depth a))

(* proper descendant *)
let is_proper_desc (d a: bin_tree_node) = is_desc d a && d <> a

(* Each node is a descendant of its parent *)
val lemma_parent_ancestor (a:non_root_node):
  Lemma (is_proper_desc a (parent a))

(* parent is a descendant of a proper ancestor *)
val lemma_parent_desc_of_proper_ancestor (d:non_root_node) (a:bin_tree_node {is_proper_desc d a}):
  Lemma (is_desc (parent d) a)

(* proper descendant depth > ancestor depth *)
val lemma_proper_desc_depth_monotonic (d a: bin_tree_node):
  Lemma (requires (is_proper_desc d a))
        (ensures (depth d > depth a))

(* Two ancestors of a node are ancestor/descendant of one another *)
val lemma_two_ancestors_related (d: bin_tree_node) (a1 a2: bin_tree_node):
  Lemma (requires (is_desc d a1 /\ is_desc d a2))
        (ensures (is_anc_desc_sym a1 a2))

(* descendant is a transitive relation *)
val lemma_proper_desc_transitive1 (a b c: bin_tree_node):
  Lemma (is_proper_desc a b /\ is_desc b c ==> is_proper_desc a c)

(* descendant is a transitive relation *)
val lemma_proper_desc_transitive2 (a b c: bin_tree_node):
  Lemma (is_desc a b /\ is_proper_desc b c ==> is_proper_desc a c)

(* two siblings are non-ancestor-descendant related *)
val lemma_siblings_non_anc_desc (n:bin_tree_node):
  Lemma (non_anc_desc (LeftChild n) (RightChild n))

(* if a and b are unrelated, then any descendant of a is unrelated to b *)
val lemma_non_anc_desc_transitive (da a b: bin_tree_node):
  Lemma (requires (non_anc_desc a b /\ is_desc da a))
        (ensures (non_anc_desc da b))

(* a proper descendant is a descendant of either left or right child *)
val lemma_proper_desc_left_or_right (d: bin_tree_node) (a: bin_tree_node {is_proper_desc d a}):
  Lemma (is_desc d (LeftChild a) /\ ~ (is_desc d (RightChild a)) \/
         is_desc d (RightChild a) /\ ~ (is_desc d (LeftChild a)))

val lemma_child_desc_is_proper_desc (d: bin_tree_node) (c: bin_tree_dir) (a: bin_tree_node):
  Lemma (requires (is_desc d (child c a)))
        (ensures (is_proper_desc d a))
        [SMTPat (is_desc d (child c a))]

val desc_dir (d: bin_tree_node) (a: bin_tree_node{is_proper_desc d a}):
  (c: bin_tree_dir {is_desc d (child c a) && not (is_desc d (sibling (child c a)))})

(* map a bit vector to a binary tree node *)
val bv_to_bin_tree_node (#n:pos) (b:bv_t n): Tot (t:bin_tree_node{depth t = n})

(* map a binary tree node to bit vector *)
val bin_tree_node_to_bv (n:non_root_node): Tot (bv_t (depth n))

val bv_to_bin_tree_consistent (#n:pos) (b:bv_t n):
  Lemma (b = bin_tree_node_to_bv (bv_to_bin_tree_node b))

val bin_tree_to_bv_consistent (n:non_root_node):
  Lemma (n = bv_to_bin_tree_node (bin_tree_node_to_bv n))

