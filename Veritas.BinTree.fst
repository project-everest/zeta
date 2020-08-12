module Veritas.BinTree

open FStar.BitVector
open FStar.Classical
open FStar.Seq

(* Inductive type that captures the descendant relationship *)
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

(* descendant is a transitive relation *)
let lemma_proper_desc_transitive2 (a b c: bin_tree_node):
  Lemma (is_desc a b /\ is_proper_desc b c ==> is_proper_desc a c) = 
  if not (is_desc a b) || not (is_proper_desc b c) then ()
  else (
    lemma_desc_transitive a b c;
    assert (is_desc a c);

    lemma_proper_desc_depth_monotonic b c;
    assert (depth b > depth c);

    lemma_desc_depth_monotonic a b;
    assert (depth a > depth c);
    ()
  )

let lemma_siblings_non_anc_desc (n:bin_tree_node):
  Lemma (non_anc_desc (LeftChild n) (RightChild n)) = 
  let lc = LeftChild n in
  let rc = RightChild n in
  if is_desc lc rc then (
    let pf_lc_rc = lemma_desc_correct2 lc rc in
    match pf_lc_rc with
    | DSelf _ -> ()
    | DLTran rc' n' pf' -> assert(rc = rc');
                           assert (n' = n);
                           lemma_desc_correct n rc pf';
                           assert(is_desc n rc);                          
                           lemma_desc_depth_monotonic n rc                         
    | DRTran _ _ _ -> ()
  )
  else if is_desc rc lc then (
    let pf_rc_lc = lemma_desc_correct2 rc lc in
    match pf_rc_lc with
    | DSelf _ -> ()
    | DLTran _ _ _ -> ()
    | DRTran lc' n' pf' -> assert (lc' = lc);
                           assert(n' = n);
                           lemma_desc_correct n lc pf';
                           assert(is_desc n lc);
                           lemma_desc_depth_monotonic n lc
  )
  else ()


let lemma_non_anc_desc_transitive (da a b: bin_tree_node):
  Lemma (requires (non_anc_desc a b /\ is_desc da a))
        (ensures (non_anc_desc da b)) = 
  if is_desc da b then
    lemma_two_ancestors_related da a b
  else if is_desc b da then
    lemma_desc_transitive b da a
  else ()

(* a proper descendant is a descendant of either left or right child *)
let rec lemma_proper_desc_left_or_right (d: bin_tree_node) (a: bin_tree_node {is_proper_desc d a}):
  Lemma (is_desc d (LeftChild a) /\ ~ (is_desc d (RightChild a)) \/
         is_desc d (RightChild a) /\ ~ (is_desc d (LeftChild a))) = 
  let d' = parent d in
  if d' = a then 
    lemma_siblings_non_anc_desc a       
  else (
    lemma_parent_ancestor d;
    lemma_two_ancestors_related d d' a;
    if is_desc d' a then (         
      lemma_proper_desc_left_or_right d' a;
      if is_desc d' (LeftChild a) && not (is_desc d' (RightChild a)) then (
        lemma_desc_transitive d d' (LeftChild a);
        if is_desc d (RightChild a) then (
          lemma_two_ancestors_related d d' (RightChild a);
          assert (is_desc (RightChild a) d');
          assert (d' <> (RightChild a));
          lemma_proper_desc_depth_monotonic (RightChild a) d';
          assert (depth (RightChild a) > depth d');
          lemma_desc_depth_monotonic d' (LeftChild a);
          ()
        )
        else ()          
      )
      else (
        lemma_desc_transitive d d' (RightChild a);
        if is_desc d (LeftChild a) then (
          lemma_two_ancestors_related d d' (LeftChild a);
          assert (is_desc (LeftChild a) d');
          assert (d' <> (LeftChild a));
          lemma_proper_desc_depth_monotonic (LeftChild a) d';
          assert (depth (LeftChild a) > depth d');
          lemma_desc_depth_monotonic d' (RightChild a);
          ()
        )
        else ()
      )
    )
    else (
      assert (d' <> a);
      lemma_proper_desc_depth_monotonic a d';
      assert (depth a > depth d');
      lemma_proper_desc_depth_monotonic d a;
      ()
    )
  )

let lemma_child_desc_is_proper_desc (d: bin_tree_node) (c: bin_tree_dir) (a: bin_tree_node):
  Lemma (requires (is_desc d (child c a)))
        (ensures (is_proper_desc d a))
        [SMTPat (is_desc d (child c a))] = 
  lemma_parent_ancestor (child c a);
  lemma_proper_desc_transitive2 d (child c a) a

let desc_dir (d:bin_tree_node) (a:bin_tree_node{is_proper_desc d a}): 
  (c: bin_tree_dir {is_desc d (child c a) && not (is_desc d (sibling (child c a)))}) = 
  lemma_proper_desc_left_or_right d a;
  if is_desc d (LeftChild a) then Left 
  else Right

let lemma_two_related_desc_same_dir (d1: bin_tree_node) 
                                    (d2: bin_tree_node)
                                    (a:bin_tree_node):
  Lemma (requires (is_proper_desc d1 a /\ 
                   is_proper_desc d2 a /\
                   is_desc d1 d2))
        (ensures (desc_dir d1 a = desc_dir d2 a)) = 
  let c1 = desc_dir d1 a in
  let c2 = desc_dir d2 a in
  if c1 = c2 then ()
  else (
    lemma_desc_transitive d1 d2 (child c2 a);
    lemma_two_ancestors_related d1 (child c2 a) (child c1 a);
    lemma_siblings_non_anc_desc a
  )

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
let rec path_from_root (a:bin_tree_node{depth a > 0}): Tot (bv_t (depth a)) 
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

(* map a binary tree node to bit vector *)
let bin_tree_node_to_bv (n:non_root_node): (bv_t (depth n)) = path_from_root n

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

let bv_to_bin_tree_consistent (#n:pos) (b:bv_t n):
  Lemma (b = bin_tree_node_to_bv (bv_to_bin_tree_node b)) = 
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

let bin_tree_to_bv_consistent (n:non_root_node):
  Lemma (n = bv_to_bin_tree_node (bin_tree_node_to_bv n)) = 
  path_from_root_bv2bin_consistent2 n

