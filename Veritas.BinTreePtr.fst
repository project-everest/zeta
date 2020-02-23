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

let lemma_pdesc_implies_desc 
  (pf:ptrfn) 
  (d: bin_tree_node)
  (a: bin_tree_node{reachable pf d a}):
  Lemma (requires (True))
        (ensures (is_desc d a)) = 
  if d = a then lemma_desc_reflexive d
  else ()

let lemma_pdesc_correct2
  (pf:ptrfn) 
  (d:bin_tree_node) 
  (a:bin_tree_node{reachable pf d a}): Tot (pdesc pf d a) =
  lemma_pdesc_implies_desc pf d a;
  lemma_desc_depth_monotonic d a;
  lemma_pdesc_correct2_aux pf d a

let lemma_reachable_reflexive (pf: ptrfn) (a: bin_tree_node):
  Lemma (reachable pf a a) = ()

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

