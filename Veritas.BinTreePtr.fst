module Veritas.BinTreePtr

open Veritas.BinTree

(* pointer based descendant relation *)
noeq type pdesc: ptrfn -> bin_tree_node -> bin_tree_node -> Type = 
  | PSelf: pf: ptrfn -> n:bin_tree_node -> pdesc pf n n
  | PTran: pf: ptrfn -> d:bin_tree_node -> d':bin_tree_node -> _:(pdesc pf d d') -> 
           a:bin_tree_node ->
           c:bin_tree_dir{Some? (pf a c) /\ Some?.v (pf a c) = d'} ->
           pdesc pf d a

let rec reachable_aux 
  (pf: ptrfn) 
  (d:bin_tree_node) 
  (a:bin_tree_node{is_proper_desc d a /\ depth d > depth a}): Tot bool
  (decreases (depth d - depth a)) = 
  let c = desc_dir d a in
  match pf a c with
  | None -> false
  | Some d' -> if d' = d then true
               else if is_desc d d' then (
                 lemma_desc_depth_monotonic d' (child c a);
                 lemma_proper_desc_depth_monotonic d d';
                 reachable_aux pf d d'
               )
               else
                 false
                 
let reachable (pf:ptrfn) (d a: bin_tree_node): Tot bool = 
  if d = a then true
  else if is_desc d a then (
    lemma_proper_desc_depth_monotonic d a;
    reachable_aux pf d a
  )
  else false

let rec lemma_pdesc_implies_desc_t (pf: ptrfn) (d a: bin_tree_node) (prf: pdesc pf d a):
  Lemma (requires (True))
        (ensures (is_desc d a))
        (decreases prf) = 
  match prf with
  | PSelf pf' n' -> lemma_desc_reflexive n'
  | PTran pf' d1 d' prf' a1 c -> 
    lemma_pdesc_implies_desc_t pf d d' prf';
    lemma_parent_ancestor (child c a);
    lemma_proper_desc_transitive2 d' (child c a) a;
    lemma_desc_transitive d d' a

let rec lemma_pdesc_correct (pf:ptrfn) (d a: bin_tree_node) (prf: pdesc pf d a):
  Lemma (requires (True))
        (ensures (reachable pf d a = true))
        (decreases prf) = 
  match prf with
  | PSelf _ _  -> ()
  | PTran _  _ d' prf' _ c -> 

    lemma_pdesc_implies_desc_t pf d d' prf';
    assert(is_desc d d');

    lemma_pdesc_correct pf d d' prf';
    assert(reachable pf d d');

    lemma_parent_ancestor (child c a);
    lemma_proper_desc_transitive2 d' (child c a) a;
    lemma_desc_transitive d d' a;
    assert(is_desc d a);

    if d = a then ()
    else (
      lemma_proper_desc_depth_monotonic d a;
      lemma_desc_transitive d d' (child c a);
      assert(desc_dir d a = c);

      if d' = d then ()
      else ()
    )

let rec lemma_pdesc_correct2_aux 
  (pf:ptrfn) 
  (d:bin_tree_node) 
  (a:bin_tree_node{reachable pf d a /\ depth d >= depth a}): 
  Tot (pdesc pf d a) 
  (decreases (depth d - depth a)) = 
  if d = a then PSelf pf d
  else (
    lemma_proper_desc_depth_monotonic d a;
    let c = desc_dir d a in    
    let d' = Some?.v (pf a c) in
    if d' = d then PTran pf d d (PSelf pf d) a c
    else (
      lemma_desc_depth_monotonic d' (child c a);
      lemma_proper_desc_depth_monotonic d d';
      let prfdd' = lemma_pdesc_correct2_aux pf d d' in
      PTran pf d d' prfdd' a c
    )
  )

let lemma_reachable_implies_desc 
  (pf:ptrfn) 
  (d: bin_tree_node)
  (a: bin_tree_node):
  Lemma (requires (reachable pf d a))
        (ensures (is_desc d a)) = 
  if d = a then lemma_desc_reflexive d
  else ()

let lemma_pdesc_correct2
  (pf:ptrfn) 
  (d:bin_tree_node) 
  (a:bin_tree_node{reachable pf d a}): Tot (pdesc pf d a) =
  lemma_reachable_implies_desc pf d a;
  lemma_desc_depth_monotonic d a;
  lemma_pdesc_correct2_aux pf d a

let lemma_reachable_reflexive (pf: ptrfn) (a: bin_tree_node):
  Lemma (reachable pf a a) = ()

let lemma_points_to_reachable (pf: ptrfn) 
                              (d: bin_tree_node) 
                              (a: bin_tree_node):
  Lemma (requires (is_proper_desc d a /\ points_to pf d a))
        (ensures (reachable pf d a)) = 
  let c = desc_dir d a in
  let prf = PTran pf d d (PSelf pf d) a c in 
  lemma_pdesc_correct pf d a prf

let rec lemma_pdesc_transitive_t (pf: ptrfn) (n1 n2 n3: bin_tree_node) 
  (prf12: pdesc pf n1 n2) (prf23: pdesc pf n2 n3): Tot (pdesc pf n1 n3) (decreases prf23) = 
  match prf23 with
  | PSelf pf _ -> prf12
  | PTran pf _ n' prf2' _ c' -> 
    let prf1' = lemma_pdesc_transitive_t pf n1 n2 n' prf12 prf2' in
    PTran pf n1 n' prf1' n3 c'

let lemma_reachable_transitive (pf: ptrfn) (a b c: bin_tree_node):
  Lemma (requires (reachable pf a b /\ reachable pf b c))
        (ensures (reachable pf a c)) = 
  let prf_ab = lemma_pdesc_correct2 pf a b in
  let prf_bc = lemma_pdesc_correct2 pf b c in
  let prf_ac = lemma_pdesc_transitive_t pf a b c prf_ab prf_bc in
  lemma_pdesc_correct pf a c prf_ac

let lemma_non_pdesc_desc_of_none (pf:ptrfn)
                                 (d:bin_tree_node)
                                 (a:bin_tree_node{is_proper_desc d a})
                                 (prf:pdesc pf d a):
   Lemma (Some? (pf a (desc_dir d a))) = 
   match prf with
   | PSelf _ _ -> ()
   | PTran _ _ d' prfdd' _ c -> 
     assert(is_desc d' (child c a));
     lemma_pdesc_implies_desc_t pf d d' prfdd';
     assert(is_desc d d');
     lemma_desc_transitive d d' (child c a)

let rec prev_in_path_aux (pf:ptrfn) 
                         (d: bin_tree_node) 
                         (a:bin_tree_node{reachable pf d a /\ d <> a}): 
  Tot (d': bin_tree_node {is_proper_desc d d' /\ reachable pf d' a /\ points_to pf d d'}) 
  (decreases (depth d - depth a)) = 
  let prf = lemma_pdesc_correct2 pf d a in
  match prf with
  | PSelf _ _ -> d  
  | PTran _ _ a' prfda' _ c  -> 

    lemma_parent_ancestor (child c a);
    lemma_proper_desc_transitive2 a' (child c a) a;
    assert(is_proper_desc a' a);
    assert(points_to pf a' a);
    assert(c = desc_dir a' a);
    if a' = d then a
    else (
      lemma_pdesc_correct pf d a' prfda';
      lemma_proper_desc_depth_monotonic a' a;
      lemma_pdesc_implies_desc_t pf d a' prfda';

      lemma_desc_depth_monotonic d a';
      let d' = prev_in_path_aux pf d a' in
      
      
      lemma_points_to_reachable pf a' a;
      lemma_reachable_transitive pf d' a' a;

      d'
    )

let prev_in_path (pf:ptrfn) (d: bin_tree_node) (a:bin_tree_node{reachable pf d a /\ d <> a}): 
  Tot (d': bin_tree_node {is_proper_desc d d' /\ reachable pf d' a /\ points_to pf d d'}) = 
  prev_in_path_aux pf d a

let lemma_non_reachable_desc_of_none (pf: ptrfn) 
                                     (d:bin_tree_node) 
                                     (a:bin_tree_node{is_proper_desc d a /\ 
                                                      None? (pf a (desc_dir d a))}):
  Lemma (not (reachable pf d a)) = 
  if reachable pf d a then (
    let prfda = lemma_pdesc_correct2 pf d a in
    lemma_non_pdesc_desc_of_none pf d a prfda
  )
  else ()

let rec lemma_extend_reachable_aux (pf:ptrfn) 
                               (d1:bin_tree_node) 
                               (a1:bin_tree_node{is_proper_desc d1 a1 /\ 
                                                                not (points_to_some pf a1 (desc_dir d1 a1))})
                               (d: bin_tree_node)
                               (a: bin_tree_node):
  Lemma (requires (reachable pf d a))
       (ensures reachable (extend_ptrfn pf d1 a1) d a) 
       (decreases (depth d - depth a))       
       = 
  lemma_reachable_implies_desc pf d a;  
  lemma_desc_depth_monotonic d a;
  let pfe = extend_ptrfn pf d1 a1 in
  let prfda = lemma_pdesc_correct2 pf d a in
  match prfda with
  | PSelf _ _ -> 
    assert(d == a);
    lemma_reachable_reflexive pfe a
  | PTran _ _ d' prfdd' _ c ->
    assert(points_to pf d' a);
    lemma_proper_desc_depth_monotonic d' a;
    lemma_pdesc_correct pf d d' prfdd';
    assert(reachable pf d d');
    
    lemma_reachable_implies_desc pf d d';
    lemma_desc_depth_monotonic d d';
    lemma_extend_reachable_aux pf d1 a1 d d';

    assert(reachable pfe d d');
    if a = a1 && desc_dir d1 a1 = desc_dir d' a then ()
    else (
      assert(pf a (desc_dir d' a) == pfe a (desc_dir d' a));
      assert(points_to pfe d' a);
      lemma_points_to_reachable pfe d' a;
      assert(reachable pfe d' a);
      lemma_reachable_transitive pfe d d' a
    )
    
let lemma_extend_reachable (pf:ptrfn) 
                           (d1:bin_tree_node) 
                           (a1:bin_tree_node{is_proper_desc d1 a1 /\ 
                                            not (points_to_some pf a1 (desc_dir d1 a1))})
                           (d: bin_tree_node)
                           (a: bin_tree_node):
  Lemma (requires (reachable pf d a))
        (ensures (reachable (extend_ptrfn pf d1 a1) d a)) =
  lemma_extend_reachable_aux pf d1 a1 d a
  
let rec lemma_reachable_feq_aux (pf1: ptrfn) (pf2: ptrfn) (d: bin_tree_node) (a: bin_tree_node):
  Lemma (requires (feq_ptrfn pf1 pf2 /\ reachable pf1 d a))
        (ensures (reachable pf2 d a)) 
        (decreases (depth d - depth a))
        = 
  lemma_reachable_implies_desc pf1 d a;  
  lemma_desc_depth_monotonic d a;        
  let prfda1 = lemma_pdesc_correct2 pf1 d a in
  match prfda1 with
  | PSelf _ _ -> lemma_reachable_reflexive pf2 a
  | PTran _ _ d' prf1dd' _ _ ->
    assert(points_to pf1 d' a);
    lemma_proper_desc_depth_monotonic d' a;
    lemma_pdesc_correct pf1 d d' prf1dd';
    assert(reachable pf1 d d');

    lemma_reachable_implies_desc pf1 d d';
    lemma_desc_depth_monotonic d d';
    lemma_reachable_feq_aux pf1 pf2 d d';
    assert(reachable pf2 d d');
    assert(points_to pf2 d' a);
    lemma_points_to_reachable pf2 d' a;
    assert(reachable pf2 d' a);
    lemma_reachable_transitive pf2 d d' a
  
let lemma_reachable_feq (pf1: ptrfn) (pf2: ptrfn) (d: bin_tree_node) (a: bin_tree_node):
  Lemma (requires (feq_ptrfn pf1 pf2))
        (ensures (reachable pf1 d a = reachable pf2 d a)) = 
  if reachable pf1 d a then
    lemma_reachable_feq_aux pf1 pf2 d a
  else if reachable pf2 d a then  
    lemma_reachable_feq_aux pf2 pf1 d a
  else ()
