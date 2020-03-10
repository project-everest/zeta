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

let rec lemma_extend_reachable_aux 
  (pf:ptrfn) 
  (d:bin_tree_node{points_to_none pf d}) 
  (a:bin_tree_node{is_proper_desc d a /\ 
                   not (points_to_some pf a (desc_dir d a)) /\
                   root_reachable pf a})
  (n: bin_tree_node):
  Lemma (requires (root_reachable pf n))
        (ensures (root_reachable (extend_ptrfn pf d a) n))  
        (decreases (depth n)) = 
  let pfe = extend_ptrfn pf d a in  
  if n = Root then 
    lemma_reachable_reflexive pfe n
  else (
    let n' = prev_in_path pf n Root in
    lemma_proper_desc_depth_monotonic n n';
    lemma_extend_reachable_aux pf d a n';
    assert(root_reachable pfe n');

    if n' = a && desc_dir d a = desc_dir n n' then ()
    else (
      assert(points_to pfe n n');
      lemma_points_to_reachable pfe n n';
      lemma_reachable_transitive pfe n n' Root
    )
  )
  
let lemma_extend_reachable 
  (pf:ptrfn) 
  (d:bin_tree_node{points_to_none pf d}) 
  (a:bin_tree_node{is_proper_desc d a /\ 
                   not (points_to_some pf a (desc_dir d a)) /\
                   root_reachable pf a})
  (n: bin_tree_node):
  Lemma (requires (root_reachable pf n))
        (ensures (root_reachable (extend_ptrfn pf d a) n)) = 
  lemma_extend_reachable_aux pf d a n

let lemma_extend_reachable_new
  (pf:ptrfn) 
  (d:bin_tree_node{points_to_none pf d}) 
  (a:bin_tree_node{is_proper_desc d a /\ 
                   not (points_to_some pf a (desc_dir d a)) /\
                   root_reachable pf a}):
  Lemma (root_reachable (extend_ptrfn pf d a) d) = 
  let pfe = extend_ptrfn pf d a in
  
  lemma_extend_reachable pf d a a;
  assert(root_reachable pfe a);

  assert(points_to pfe d a);
  lemma_points_to_reachable pfe d a;
  lemma_reachable_transitive pfe d a Root

(* extends confers reachability only to the new node *)
let rec lemma_extend_not_reachable_aux
  (pf:ptrfn) 
  (d:bin_tree_node{points_to_none pf d}) 
  (a:bin_tree_node{is_proper_desc d a /\ 
                   not (points_to_some pf a (desc_dir d a)) /\
                   root_reachable pf a})
  (n: bin_tree_node):
  Lemma (requires (not (root_reachable pf n) /\ n <> d))
        (ensures (not (root_reachable (extend_ptrfn pf d a) n))) 
        (decreases (depth n)) =         
  let pfe = extend_ptrfn pf d a in
  if root_reachable pfe n then (
    let n' = prev_in_path pfe n Root in
    lemma_proper_desc_depth_monotonic n n';
    assert(points_to pfe n n');
    if n' = d then ()
    else if root_reachable pf n' then 
      if n' = a && desc_dir n n' = desc_dir d a then ()
      else (
        lemma_points_to_reachable pf n n';
        lemma_reachable_transitive pf n n' Root
      )
    else 
      lemma_extend_not_reachable_aux pf d a n'    
  )
  else ()

let lemma_extend_not_reachable
  (pf:ptrfn) 
  (d:bin_tree_node{points_to_none pf d}) 
  (a:bin_tree_node{is_proper_desc d a /\ 
                   not (points_to_some pf a (desc_dir d a)) /\
                   root_reachable pf a})
  (n: bin_tree_node):
  Lemma (requires (not (root_reachable pf n) /\ n <> d))
        (ensures (not (root_reachable (extend_ptrfn pf d a) n))) = 
  lemma_extend_not_reachable_aux pf d a n

let rec lemma_extendcut_reachable_aux
  (pf:ptrfn)
  (d:bin_tree_node{points_to_none pf d})
  (a:bin_tree_node{is_proper_desc d a /\ 
                    points_to_some pf a (desc_dir d a) /\
                    is_proper_desc (pointed_node pf a (desc_dir d a)) d /\ 
                    root_reachable pf a})
  (n: bin_tree_node):
  Lemma (requires (root_reachable pf n))
        (ensures (root_reachable (extendcut_ptrfn pf d a) n)) 
        (decreases (depth n)) = 
  let pfe = extendcut_ptrfn pf d a in
  if n = Root then
    lemma_reachable_reflexive pfe n
  else (
    let n' = prev_in_path pf n Root in
    lemma_proper_desc_depth_monotonic n n';
    lemma_extendcut_reachable_aux pf d a n';
    assert(root_reachable pfe n');

    assert(points_to pf n n');
    if n' = a && desc_dir d a = desc_dir n n' then (
      assert(points_to pfe d n');
      lemma_points_to_reachable pfe d n';
      assert(points_to pfe n d);
      lemma_points_to_reachable pfe n d;
      lemma_reachable_transitive pfe n d n';
      lemma_reachable_transitive pfe n n' Root
    )
    else (
      assert(points_to pfe n n');
      lemma_points_to_reachable pfe n n';
      lemma_reachable_transitive pfe n n' Root
    )
  )
  
let lemma_extendcut_reachable 
  (pf:ptrfn)
  (d:bin_tree_node{points_to_none pf d})
  (a:bin_tree_node{is_proper_desc d a /\ 
                    points_to_some pf a (desc_dir d a) /\
                    is_proper_desc (pointed_node pf a (desc_dir d a)) d /\ 
                    root_reachable pf a})
  (n: bin_tree_node):
  Lemma (requires (root_reachable pf n))
        (ensures (root_reachable (extendcut_ptrfn pf d a) n)) = 
  lemma_extendcut_reachable_aux pf d a n

let lemma_extendcut_reachable_new
  (pf:ptrfn)
  (d:bin_tree_node{points_to_none pf d})
  (a:bin_tree_node{is_proper_desc d a /\ 
                    points_to_some pf a (desc_dir d a) /\
                    is_proper_desc (pointed_node pf a (desc_dir d a)) d /\ 
                    root_reachable pf a}):
  Lemma (root_reachable (extendcut_ptrfn pf d a) d) = 
  let pfe = extendcut_ptrfn pf d a in
  lemma_extendcut_reachable pf d a a;
  assert(root_reachable pfe a);
  assert(points_to pfe d a);
  lemma_points_to_reachable pfe d a;
  lemma_reachable_transitive pfe d a Root

let rec lemma_extendcut_not_reachable_aux
  (pf:ptrfn)
  (d:bin_tree_node{points_to_none pf d})
  (a:bin_tree_node{is_proper_desc d a /\ 
                    points_to_some pf a (desc_dir d a) /\
                    is_proper_desc (pointed_node pf a (desc_dir d a)) d /\ 
                    root_reachable pf a})
  (n: bin_tree_node):
  Lemma (requires (not (root_reachable pf n) /\ n <> d))
        (ensures (not (root_reachable (extendcut_ptrfn pf d a) n)))
        (decreases (depth n)) = 
  let pfe = extendcut_ptrfn pf d a in
  if root_reachable pfe n then (
    let n' = prev_in_path pfe n Root in
    assert(points_to pfe n n');
    if n' = a && desc_dir n n' = desc_dir d a then ()
    else if n' = d then (
      let d' = pointed_node pf a (desc_dir d a) in
      assert(n = d');
    
      lemma_points_to_reachable pf d' a;
      lemma_reachable_transitive pf d' a Root
    )
    else (
      assert(points_to pf n n');
      lemma_points_to_reachable pf n n';
      lemma_proper_desc_depth_monotonic n n';
      if root_reachable pf n' then 
         lemma_reachable_transitive pf n n' Root
      else
        lemma_extendcut_not_reachable_aux pf d a n'
    )
  )
  else ()

let lemma_extendcut_not_reachable 
  (pf:ptrfn)
  (d:bin_tree_node{points_to_none pf d})
  (a:bin_tree_node{is_proper_desc d a /\ 
                    points_to_some pf a (desc_dir d a) /\
                    is_proper_desc (pointed_node pf a (desc_dir d a)) d /\ 
                    root_reachable pf a})
  (n: bin_tree_node):
  Lemma (requires (not (root_reachable pf n) /\ n <> d))
        (ensures (not (root_reachable (extendcut_ptrfn pf d a) n))) = 
  lemma_extendcut_not_reachable_aux pf d a n

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

let rec lemma_desc_of_prev_not_reachable_aux (pf:ptrfn)
                                             (d1:bin_tree_node)
                                             (a:bin_tree_node)
                                             (d2:bin_tree_node):
  Lemma (requires (reachable pf d1 a /\ d1 <> a /\
                   is_proper_desc d1 d2 /\
                   is_proper_desc d2 (prev_in_path pf d1 a)))
        (ensures (not (reachable pf d2 a))) 
        (decreases (depth d2)) = 
  let pd1 = prev_in_path pf d1 a in
  if reachable pf d2 a then (
    lemma_reachable_implies_desc pf pd1 a;
    lemma_proper_desc_transitive1 d2 pd1 a;
    let pd2 = prev_in_path pf d2 a in
    lemma_two_ancestors_related d2 pd1 pd2;
    if pd1 = pd2 then (
      assert(points_to pf d1 pd1);
      assert(points_to pf d2 pd1);
      let c1 = desc_dir d1 pd1 in
      let c2 = desc_dir d2 pd2 in
      if c1 = c2 then ()
      else (
        lemma_desc_transitive d1 d2 (child c2 pd1);
        lemma_two_ancestors_related d1 (child c2 pd1) (child c1 pd1);
        lemma_siblings_non_anc_desc pd1
      )
    )
    else if is_desc pd2 pd1 then (
      assert(is_proper_desc pd2 pd1);
      lemma_proper_desc_depth_monotonic d2 pd2;
      lemma_proper_desc_transitive1 d1 d2 pd2;
      lemma_desc_of_prev_not_reachable_aux pf d1 a pd2;      
      ()
    )
    else (
      assert(is_proper_desc pd1 pd2);
      lemma_proper_desc_depth_monotonic d2 pd1;
      lemma_desc_of_prev_not_reachable_aux pf d2 a pd1;
      ()
    )
  )
  else ()

let lemma_desc_of_prev_not_reachable (pf:ptrfn)
                                     (d1:bin_tree_node)
                                     (a:bin_tree_node)
                                     (d2:bin_tree_node):
  Lemma (requires (reachable pf d1 a /\ d1 <> a /\
                   is_proper_desc d1 d2 /\
                   is_proper_desc d2 (prev_in_path pf d1 a)))
        (ensures (not (reachable pf d2 a))) = 
  lemma_desc_of_prev_not_reachable_aux pf d1 a d2

let lemma_prev_in_path_feq (pf1: ptrfn) 
                           (pf2: ptrfn) 
                           (d:bin_tree_node) 
                           (a:bin_tree_node):
   Lemma (requires (feq_ptrfn pf1 pf2 /\ reachable pf1 d a /\ d <> a))
         (ensures (prev_in_path pf1 d a = prev_in_path pf2 d a)) = 
   let pd1 = prev_in_path pf1 d a in
   let pd2 = prev_in_path pf2 d a in
   lemma_two_ancestors_related d pd1 pd2;
   if pd1 = pd2 then ()
   else if is_desc pd1 pd2 then 
     lemma_desc_of_prev_not_reachable pf2 d a pd1       
   else 
     lemma_desc_of_prev_not_reachable pf1 d a pd2

let rec lemma_points_to_not_reachable_between_aux (pf:ptrfn)
                                                  (d:bin_tree_node)
                                                  (a:bin_tree_node)
                                                  (pd:bin_tree_node)
                                                  (n:bin_tree_node)
  : Lemma (requires (reachable pf pd a /\
                     is_proper_desc d pd /\
                     points_to pf d pd /\
                     is_proper_desc d n /\
                     is_proper_desc n pd))
          (ensures (not (reachable pf n a)))
          (decreases (depth n)) = 
          
  lemma_reachable_implies_desc pf pd a;
  lemma_proper_desc_transitive1 n pd a;
  assert(is_proper_desc n a);

  if reachable pf n a then (
    let pn = prev_in_path pf n a in
    lemma_two_ancestors_related n pn pd;
    if pn = pd then (
      let c1 = desc_dir d pd in
      let c2 = desc_dir n pn in
      if c1 = c2 then()
      else (
        lemma_desc_transitive d n (child c2 pn);
        lemma_two_ancestors_related d (child c1 pn) (child c2 pn);
        lemma_siblings_non_anc_desc pn
      )
    )
    else if is_desc pn pd then (
      lemma_proper_desc_depth_monotonic n pn;
      lemma_proper_desc_transitive1 d n pn;
      lemma_points_to_not_reachable_between_aux pf d a pd pn
    )
    else 
      lemma_desc_of_prev_not_reachable pf n a pd    
  )
  else ()

let lemma_points_to_not_reachable_between (pf:ptrfn)
                                          (d:bin_tree_node)
                                          (a:bin_tree_node)
                                          (pd:bin_tree_node)
                                          (n:bin_tree_node)
  : Lemma (requires (reachable pf pd a /\
                     is_proper_desc d pd /\
                     points_to pf d pd /\
                     is_proper_desc d n /\
                     is_proper_desc n pd))
          (ensures (not (reachable pf n a))) = 
 lemma_points_to_not_reachable_between_aux pf d a pd n

let lemma_points_to_is_prev (pf:ptrfn)
                            (d:bin_tree_node)
                            (a:bin_tree_node)
                            (pd:bin_tree_node):
  Lemma (requires (reachable pf d a /\ 
                   reachable pf pd a /\ 
                   is_proper_desc d pd /\
                   d <> a /\
                   points_to pf d pd))
        (ensures (prev_in_path pf d a = pd)) = 
  let pd' = prev_in_path pf d a in
  lemma_two_ancestors_related d pd' pd;
  if pd' = pd then ()
  else if is_desc pd' pd then 
    lemma_points_to_not_reachable_between pf d a pd pd'
  else
    lemma_points_to_not_reachable_between pf d a pd' pd
