module Veritas.Merkle

open FStar.BitVector
open FStar.Classical
open FStar.Seq
open Veritas.Memory

(* Traverse down a binary tree from a start node (sn) based on a bit vector *)
let rec traverse_bin_tree (#n:pos) (b:bv_t n) (sn:bin_tree_node): Tot bin_tree_node = 
  if n = 1 
  then if index b 0 then RightChild sn else LeftChild sn
  else (
    let tn' = traverse_bin_tree #(n-1) (slice b 0 (n-1)) sn in
    if index b (n-1) then RightChild tn' else LeftChild tn'
  )

(* Traversing adds bit vector length to the depth *)
let rec traverse_adds_size_to_depth (#n:pos) (b:bv_t n) (sn:bin_tree_node): 
  Lemma (requires (True))
        (ensures (depth (traverse_bin_tree b sn) = n + depth sn)) = 
  if (n = 1) 
  then () 
  else traverse_adds_size_to_depth #(n-1) (slice b 0 (n-1)) sn

(* Map a bit vector to a binary tree node by traversing from the root *)
let bv_to_bin_tree_node (#n:pos) (b:bv_t n): Tot (t:bin_tree_node{depth t = n}) = 
  traverse_adds_size_to_depth b Root; traverse_bin_tree b Root

(* Given a binary tree node return the path from root as a binary vector *)
let rec path_from_root (a:bin_tree_node{depth a > 0}): Tot (b:bv_t (depth a)) 
  (decreases (depth a)) = 
  if depth a = 1 
  then (match a with
       | LeftChild a' -> zero_vec #1
       | RightChild a' -> ones_vec #1
       )
  else (match a with
       | LeftChild a' -> (append (path_from_root a') (zero_vec #1))
       | RightChild a' -> (append (path_from_root a') (ones_vec #1))
       )

(* path_from_root and bv_to_bin_tree_node are inverse operations *)
let rec path_from_root_bv2bin_consistent_aux (#n:pos) (b:bv_t n) (i:nat{i < n}):
  Lemma (index (path_from_root (bv_to_bin_tree_node b)) i = index b i)
  = 
  if n = 1 then ()  
  else (
    if i = n - 1 
    then ()
    else path_from_root_bv2bin_consistent_aux #(n-1) (slice b 0 (n-1)) i
  )

(* path_from_root and bv_to_bin_tree_node are inverse operations *)
let path_from_root_bv2bin_consistent (#n:pos) (b:bv_t n):
  Lemma (path_from_root (bv_to_bin_tree_node b) = b) = 
  let b' = path_from_root (bv_to_bin_tree_node b) in
  let aux (i:nat{i < n}): Lemma ((index b' i) = (index b i)) = 
    path_from_root_bv2bin_consistent_aux b i  
  in
  forall_intro aux; lemma_eq_intro b b'

(* path_from_root and bv_to_bin_tree_node are inverse operations - II *)
let rec path_from_root_bv2bin_consistent2 (tn:bin_tree_node{depth tn > 0}):
  Lemma (requires (True)) 
        (ensures bv_to_bin_tree_node (path_from_root tn) = tn)
  (decreases (depth tn)) =
  let n = depth tn in
  if n = 1 then ()
  else match tn with 
       | LeftChild tn' -> 
           let p' = path_from_root tn' in
           append_slices p' (zero_vec #1);
           path_from_root_bv2bin_consistent2 tn'
       | RightChild tn' -> 
           let p' = path_from_root tn' in
           append_slices p' (ones_vec #1);
           path_from_root_bv2bin_consistent2 tn'

let hashfn (m:merkle_payload): hash_value = admit()

(* 
 * map each 256 bit address in memory to a leaf node of the 
 * merkle tree
 *)
let addr_to_merkle_leaf (a:addr): Tot merkle_leaf_addr = 
  bv_to_bin_tree_node a

(* Inverse of addr_to_merkle_leaf *)
let merkle_leaf_to_addr (ma:merkle_leaf_addr): Tot (a:addr{addr_to_merkle_leaf a = ma}) =
  path_from_root_bv2bin_consistent2 ma; path_from_root ma

let lemma_addr_merkle_inv (a:addr):
  Lemma (merkle_leaf_to_addr (addr_to_merkle_leaf a) = a) = 
  path_from_root_bv2bin_consistent a

let lemma_merkle_equal_implies_addr_equal (a1:addr) (a2:addr):
  Lemma (requires (addr_to_merkle_leaf a1 = addr_to_merkle_leaf a2))
        (ensures (a1 = a2)) = 
  lemma_addr_merkle_inv a1;
  lemma_addr_merkle_inv a2

let lemma_addr_equal_implies_merkle_equal (m1:merkle_leaf_addr) (m2:merkle_leaf_addr):
  Lemma (requires (merkle_leaf_to_addr m1 = merkle_leaf_to_addr m2))
        (ensures (m1 = m2)) = ()

type desc: bin_tree_node -> bin_tree_node -> Type = 
  | DSelf: n:bin_tree_node -> desc n n
  | DLTran: a:bin_tree_node -> d:bin_tree_node -> _:(desc d a) -> desc (LeftChild d) a
  | DRTran: a:bin_tree_node -> d:bin_tree_node -> _:(desc d a) -> desc (RightChild d) a

let rec is_desc_aux (d a: bin_tree_node): 
  Tot bool = 
  if d = a then true
  else 
    match d with
    | Root -> false
    | LeftChild p -> is_desc_aux p a 
    | RightChild p -> is_desc_aux p a

let rec lemma_desc_correct (d a: bin_tree_node) (pf: desc d a) : 
    Lemma (requires (True))
          (ensures (is_desc_aux d a = true))
          (decreases pf) = 
    match pf with
    | DSelf a' -> ()
    | DLTran a' d' pf' -> lemma_desc_correct d' a pf'
    | DRTran a' d' pf' -> lemma_desc_correct d' a pf'

let rec lemma_desc_correct2 (d: bin_tree_node) (a: bin_tree_node{is_desc_aux d a}): Tot (desc d a) = 
  if d = a then DSelf d
  else 
    match d with
    | Root -> DSelf d
    | LeftChild d' -> DLTran a d' (lemma_desc_correct2 d' a)
    | RightChild d' -> DRTran a d' (lemma_desc_correct2 d' a) 

let is_desc d a = is_desc_aux d a

let rec lemma_root_is_univ_ancestor_t (a: bin_tree_node): (desc a Root) = 
  match a with
  | Root -> DSelf Root
  | LeftChild a' -> DLTran Root a' (lemma_root_is_univ_ancestor_t a')
  | RightChild a' -> DRTran Root a' (lemma_root_is_univ_ancestor_t a')

let lemma_root_is_univ_ancestor (a: bin_tree_node):
  Lemma (is_desc a Root) = 
  let pf = lemma_root_is_univ_ancestor_t a in
  lemma_desc_correct a Root pf

let lemma_desc_reflexive (a: bin_tree_node):
  Lemma (is_desc a a) = 
  lemma_desc_correct a a (DSelf a)

let lemma_root_non_desc_t (a: bin_tree_node) (pf: desc Root a):
  Lemma (a = Root) = ()

let rec lemma_desc_transitive_t (a b c: bin_tree_node) (pf1: desc a b) (pf2: desc b c): desc a c = 
  match pf1 with
  | DSelf b' -> pf2
  | DLTran b' a' pf' -> let pa'c = lemma_desc_transitive_t a' b c pf' pf2 in
                        DLTran c a' pa'c
  | DRTran b' a' pf' -> let pa'c = lemma_desc_transitive_t a' b c pf' pf2 in
                        DRTran c a' pa'c

let lemma_desc_transitive (a b c: bin_tree_node):
  Lemma (is_desc a b /\ is_desc b c ==> is_desc a c) = 
  if is_desc a b && is_desc b c then (
    let pf_ab = lemma_desc_correct2 a b in
    let pf_bc = lemma_desc_correct2 b c in
    let pf_ac = lemma_desc_transitive_t a b c pf_ab pf_bc in
    lemma_desc_correct a c pf_ac
  )
  else ()

let rec lemma_desc_depth_monotonic_t (d a: bin_tree_node) (pf: desc d a):
  Lemma (ensures (depth d >= depth a)) = 
  match pf with
  | DSelf d' -> ()
  | DLTran a' d' pf' -> lemma_desc_depth_monotonic_t d' a' pf'
  | DRTran a' d' pf' -> lemma_desc_depth_monotonic_t d' a' pf'

let lemma_desc_depth_monotonic (d a: bin_tree_node):
  Lemma (requires (is_desc d a))
        (ensures (depth d >= depth a)) = 
  let pf = lemma_desc_correct2 d a in
  lemma_desc_depth_monotonic_t d a pf

(* Each node is a descendant of its parent *)
let lemma_parent_ancestor (a: bin_tree_node{~(Root? a)}):
  Lemma (is_proper_desc a (parent a)) = ()

let lemma_parent_desc_of_proper_ancestor (d:bin_tree_node{~(Root? d)}) (a:bin_tree_node {is_proper_desc d a}):
  Lemma (is_desc (parent d) a) = ()

let lemma_proper_desc_depth_monotonic (d a: bin_tree_node):
  Lemma (requires (is_proper_desc d a))
        (ensures (depth d > depth a)) =
  if Root? d then ()
  else 
    let p = parent d in
    lemma_parent_desc_of_proper_ancestor d a;
    lemma_desc_depth_monotonic p a

(* Two ancestors of a node are ancestor/descendant of one another *)
let rec lemma_two_ancestors_related (d: bin_tree_node) (a1 a2: bin_tree_node):
  Lemma (requires (is_desc d a1 /\ is_desc d a2))
        (ensures (is_desc a1 a2 \/ is_desc a2 a1)) =   
  if d = a1 || d = a2 then ()
  (* d is a proper desc of a1 and a2 *)
  else
  match d with
  | Root -> ()
  | LeftChild p -> lemma_parent_desc_of_proper_ancestor d a1;
                   lemma_parent_desc_of_proper_ancestor d a2;
                   assert(is_desc p a1);
                   assert(is_desc p a2);
                   lemma_two_ancestors_related p a1 a2
  | RightChild p -> lemma_parent_desc_of_proper_ancestor d a1;
                   lemma_parent_desc_of_proper_ancestor d a2;
                   assert(is_desc p a1);
                   assert(is_desc p a2);
                   lemma_two_ancestors_related p a1 a2

(* descendant is a transitive relation *)
let lemma_proper_desc_transitive1 (a b c: bin_tree_node):
  Lemma (is_proper_desc a b /\ is_desc b c ==> is_proper_desc a c) = 
  if not (is_proper_desc a b) || not (is_desc b c) then ()
  else (
    lemma_desc_transitive a b c;
    assert (is_desc a c);
    
    lemma_proper_desc_depth_monotonic a b;
    assert (depth a > depth b);
    
    lemma_desc_depth_monotonic b c;
    assert (depth a > depth c);
    ()
  ) 
   
