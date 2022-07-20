module Zeta.BinTree

open FStar.BitVector
open FStar.Classical
open FStar.Seq
open Zeta.SeqAux

(* Inductive type that captures the descendant relationship *)
type desc: bin_tree_node -> bin_tree_node -> Type = 
  | DSelf: n:bin_tree_node -> desc n n
  | DLTran: a:bin_tree_node -> d:bin_tree_node -> _:(desc d a) -> desc (LeftChild d) a
  | DRTran: a:bin_tree_node -> d:bin_tree_node -> _:(desc d a) -> desc (RightChild d) a

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

let is_desc_eq (d a: bin_tree_node)
  : Lemma (is_desc d a == is_desc_aux d a)
  = ()
  
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

(* Map a bit vector to a binary tree node by traversing from the root *)
let rec bv_to_bin_tree_node (#n:nat) (b:bv_t n): Tot (t:bin_tree_node{depth t = n}) (decreases n) =
  if n = 0 then Root
  else
    let b' = hprefix b in
    let n' = bv_to_bin_tree_node #(n-1) b' in
    if telem b then RightChild n' else LeftChild n'

(* Given a binary tree node return the path from root as a binary vector *)
let rec bin_tree_node_to_bv (a:bin_tree_node): Tot (v: bv_t (depth a) { bv_to_bin_tree_node v = a })
  (decreases (depth a)) =
  match a with
  | Root -> FStar.Seq.empty #bool
  | LeftChild a' ->
    let v' = bin_tree_node_to_bv a' in
    let v = append1 v' false in
    lemma_prefix1_append v' false;
    v
  | RightChild a' ->
    let v' = bin_tree_node_to_bv a' in
    let v = append1 v' true in
    lemma_prefix1_append v' true;
    v

let rec bv_to_bin_tree_consistent (#n:nat) (b:bv_t n):
  Lemma (ensures (let t = bv_to_bin_tree_node b in
                  b = bin_tree_node_to_bv t))
        (decreases n) =
  let t = bv_to_bin_tree_node b in
  let b2 = bin_tree_node_to_bv t in
  if n = 0 then lemma_empty b
  else
    let b' = hprefix b in
    let t' = bv_to_bin_tree_node #(n-1) b' in
    bv_to_bin_tree_consistent #(n-1) b';
    assert(bin_tree_node_to_bv t' = b');
    let aux (i: nat{i < n}):
      Lemma (ensures (index b2 i = index b i))
            [SMTPat (index b2 i = index b i)] = ()
    in
    lemma_eq_intro b b2

(* a is a common ancestor of d1 and d2 *)
let is_common_ancestor a d1 d2
  = is_desc d1 a && is_desc d2 a

(* a is the least common ancestor of d1 and d2 *)
let is_least_common_ancestor a d1 d2
  = is_common_ancestor a d1 d2 /\
    (forall a'. is_common_ancestor a' d1 d2 ==> is_desc a a')

let rec least_common_ancestor_aux (d1 d2: bin_tree_node)
  = lemma_root_is_univ_ancestor d1;
    lemma_root_is_univ_ancestor d2;    
    if is_desc d2 d1 then d1
    else if is_desc d1 d2 then d2
    else least_common_ancestor_aux (parent d1) (parent d2) 

(* if a is an ancestor of d, then a is the least common ancestor of d & a *)
let anc_is_least_common_ancestor (a d: bin_tree_node)
  : Lemma (ensures (is_desc d a ==> is_least_common_ancestor a d a))
          [SMTPat (is_desc d a)]
  = if is_desc d a then
    begin
      assert (is_common_ancestor a d a);
      let aux (a':_)
        : Lemma (ensures (is_common_ancestor a' d a ==> is_desc a a'))
        = ()
      in
      forall_intro aux
    end

let rec least_common_ancestor_aux_is_correct (d1 d2: bin_tree_node)
  : Lemma (ensures (is_least_common_ancestor (least_common_ancestor_aux d1 d2) d1 d2))
          (decreases (depth d1))
          [SMTPat (least_common_ancestor_aux d1 d2)]
  = let a = least_common_ancestor_aux d1 d2 in
    lemma_root_is_univ_ancestor d1;
    lemma_root_is_univ_ancestor d2;    
    if is_desc d2 d1 then
      anc_is_least_common_ancestor d1 d2
    else if is_desc d1 d2 then
      anc_is_least_common_ancestor d2 d1
    else
      let p1 = parent d1 in
      let p2 = parent d2 in
      assert (a = least_common_ancestor_aux p1 p2);
      least_common_ancestor_aux_is_correct p1 p2;
      assert (is_least_common_ancestor a p1 p2);
      assert (is_common_ancestor a d1 d2);

      let aux (a':_)
        : Lemma (ensures (is_common_ancestor a' d1 d2 ==> is_desc a a'))
        = if is_common_ancestor a' d1 d2 then ()
      in
      forall_intro aux

(* compute the least common ancestor of d1 and d2 *)
let least_common_ancestor (d1 d2: bin_tree_node)
  : a:_{is_least_common_ancestor a d1 d2}
  = least_common_ancestor_aux d1 d2

let least_common_ancestor_is_uniq (a1 a2 d1 d2: bin_tree_node)
  : Lemma (requires (is_least_common_ancestor a1 d1 d2 /\ is_least_common_ancestor a2 d1 d2))
          (ensures (a1 = a2))
  = eliminate forall a'. is_common_ancestor a' d1 d2 ==> is_desc a1 a' with a2;
    assert (is_desc a1 a2);

    assert (forall a'. is_common_ancestor a' d1 d2 ==> is_desc a2 a');
    eliminate forall a'. is_common_ancestor a' d1 d2 ==> is_desc a2 a' with a1;
    assert (is_desc a2 a1);

    if a1 <> a2 then
    begin
      lemma_proper_desc_depth_monotonic a1 a2;
      lemma_proper_desc_depth_monotonic a2 a1;
      ()
    end

(* if d1 and d2 are not anc-desc then the least common ancestor is a proper ancestor *)
let proper_least_common_ancestor (d1 d2:_)
  : Lemma (ensures (let a = least_common_ancestor d1 d2 in
                    not (is_anc_desc_sym d1 d2) ==> is_proper_desc d1 a /\ is_proper_desc d2 a))
          [SMTPat (least_common_ancestor d1 d2)]
  = if not (is_anc_desc_sym d1 d2) then
      ()



let lt (n1 n2: bin_tree_node): bool
  = if is_anc_desc_sym n1 n2 then
      depth n1 < depth n2
    else 
      let a = least_common_ancestor n1 n2 in
      assert (a <> n1 && a <> n2);
      
      admit()
