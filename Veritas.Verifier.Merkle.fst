module Veritas.Verifier.Merkle

open Veritas.BinTreePtr
open Veritas.EAC
open Veritas.Interleave

module BP=Veritas.BinTreePtr

(* A log entry not referencing key k does not affect the eac_value of k *)
let lemma_eac_value_unchanged (itsl: TL.eac_log{I.length itsl > 0}) (k:merkle_key):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   let ke = V.key_of e in
                   ke <> k))
        (ensures (let n = I.length itsl in
                  let itsl' = I.prefix itsl (n - 1) in 
                  eac_value itsl k = eac_value itsl' k)) = 
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  let e = I.index itsl (n - 1) in
  let ke = V.key_of e in

  let es' = TL.eac_state_of_key itsl' k in
  let es = TL.eac_state_of_key itsl k in
  
  lemma_fullprefix_equal itsl;
  lemma_eac_state_of_key_valid itsl k;
  lemma_eac_state_of_key_valid itsl' k;
  lemma_eac_state_same itsl (n - 1) k;
  assert(es <> EACFail);
  assert(es = es');

  match es with
  | EACInit -> 
    lemma_eac_value_init itsl' k;
    lemma_eac_value_init itsl k
    
  | EACInStore m v -> 
  
    (* k is in store of tid after itsl' *)
    let tidk = stored_tid itsl' k in
    assert(store_contains (TL.thread_store itsl' tidk) k);

    (* thread id where element e goes *)
    let tid = thread_id_of itsl (n - 1) in

    if tid = tidk then
      admit()
    else
      admit()
      
  | EACEvictedMerkle v -> admit()
  | EACEvictedBlum v t j -> admit()

(* for a merkle key k, the eac_value along direction c is either empty or points to a descendant *)
let lemma_eac_value_empty_or_points_to_desc
  (itsl: TL.eac_log)
  (k:merkle_key)
  (c:bin_tree_dir):
  Lemma (let ev = to_merkle_value (eac_value itsl k) in      // eac_value of k
         let dh = desc_hash_dir ev c in                      // desc hash along direction c 
         let kc = child c k in                               // child of k along direction c          
         dh = Empty \/
         is_desc (Desc?.k dh) kc) = 
             
  admit()                 

let eac_ptrfn_aux (itsl: TL.eac_log) (n:bin_tree_node) (c:bin_tree_dir):
  option (d:bin_tree_node{is_desc d (child c n)}) = 
  if depth n >= key_size then None
  else (
    let ev = to_merkle_value (eac_value itsl n) in
    let dh = desc_hash_dir ev c in
    lemma_eac_value_empty_or_points_to_desc itsl n c;
    match dh with
    | Empty -> None
    | Desc d _ _ -> Some d
  )

(* eac pointer function *)
let eac_ptrfn (itsl: TL.eac_log): ptrfn =
  eac_ptrfn_aux itsl

(* eac_ptrfn value is the same as the eac_value *)
let lemma_eac_ptrfn (itsl: TL.eac_log) (k: merkle_key) (c:bin_tree_dir) :
  Lemma (requires True)
        (ensures (let pf = eac_ptrfn itsl in
                  let mv = eac_merkle_value itsl k in
                  mv_points_to_none mv c /\ pf k c = None \/                   
                  mv_points_to_some mv c /\ is_desc (mv_pointed_key mv c) (child c k) /\
                  pf k c = Some (mv_pointed_key mv c)))
        [SMTPat (eac_ptrfn itsl k c)] = 
  let pf = eac_ptrfn itsl in
  let mv = eac_merkle_value itsl k in
  if mv_points_to_none mv c then ()
  else (
    let kd = mv_pointed_key mv c in
    lemma_eac_value_empty_or_points_to_desc itsl k c;
    ()
  )

let root_reachable (itsl: TL.eac_log) (k:key): bool = 
  let pf = eac_ptrfn itsl in
  BP.root_reachable pf k

(* a key is root reachable iff its eac_state is not EACInit *)
let lemma_not_init_equiv_root_reachable (itsl: TL.eac_log) (k:key{k <> Root}):
  Lemma (not (is_eac_state_init itsl k) <==> root_reachable itsl k) = 
  admit()

let rec first_root_reachable_ancestor (itsl: TL.eac_log) (k:key):
  Tot (k':key{root_reachable itsl k' /\
              is_desc k k'}) 
  (decreases (depth k)) = 
  let pf = eac_ptrfn itsl in
  
  if root_reachable itsl k then (
    lemma_desc_reflexive k;
    k
  )
  else (
    (* root is reachable from itself *)
    lemma_reachable_reflexive pf Root; 

    (* since k is not root_reachable, k cannot be Root *)
    assert(k <> Root);

    (* so, k has a parent *)
    let kp = parent k in

    (* recurse ... *)
    let k' = first_root_reachable_ancestor itsl kp in
    
    lemma_parent_ancestor k;
    lemma_desc_transitive k kp k';
    k'
  )

(* the ancestor who holds the proof of the value of key k *)
let proving_ancestor (itsl: TL.eac_log) (k:key{k <> Root}):
  k':key{is_proper_desc k k'} = 
  let pf = eac_ptrfn itsl in
  lemma_not_init_equiv_root_reachable itsl k;
  
  if root_reachable itsl k then 
    //assert(not (is_eac_state_init itsl k));
    prev_in_path pf k Root  
  else first_root_reachable_ancestor itsl k

let lemma_proving_ancestor_root_reachable (itsl: TL.eac_log) (k:key{k <> Root}):
  Lemma (let k' = proving_ancestor itsl k in
         root_reachable itsl k') = admit()

let lemma_proving_ancestor_greatest_depth (itsl: TL.eac_log) (k:key{k <> Root}) (k2: key{is_proper_desc k k2}):  
  Lemma (requires (root_reachable itsl k2))
        (ensures  (let k' = proving_ancestor itsl k in
                   depth k2 <= depth k')) = admit()

(* after the first add the proving ancestor always points to self *)
let lemma_proving_ancestor_points_to_self (itsl: TL.eac_log) (k:key{k <> Root}):
  Lemma (requires not (is_eac_state_init itsl k))
        (ensures (mv_points_to (eac_merkle_value itsl (proving_ancestor itsl k))
                               (desc_dir k (proving_ancestor itsl k))
                               k)) =
  admit()                               
   
(* before the first add the proving ancestor points to none or to a key that is not an ancestor *)
let lemma_proving_ancestor_initial (itsl: TL.eac_log) (k:key{k <> Root}):
  Lemma (requires (is_eac_state_init itsl k))
        (ensures (let k' = proving_ancestor itsl k in
                  let v' = eac_merkle_value itsl k' in
                  let c = desc_dir k k' in
                  mv_points_to_none v' c \/
                  not (is_desc k (mv_pointed_key v' c)))) =
  let pf = eac_ptrfn itsl in                  
  let k' = proving_ancestor itsl k in                  
  let v' = eac_merkle_value itsl k' in
  let c = desc_dir k k' in

  (* k' is root reachable *)
  lemma_proving_ancestor_root_reachable itsl k;
  assert(root_reachable itsl k');  

  (* k is not root reachable since it is in initial state *)
  lemma_not_init_equiv_root_reachable itsl k;
  assert(not (root_reachable itsl k ));

  (* points to none - nothing to prove *)
  if mv_points_to_none v' c then ()
  else
    (* k' points to k2 along direction c *)
    let k2 = mv_pointed_key v' c in

    (* k2 is a proper descendant of k' *)
    lemma_eac_ptrfn itsl k' c;
    lemma_parent_ancestor (child c k');
    //assert(is_desc k2 (child c k'));
    lemma_proper_desc_transitive1 k2 (child c k') k';
    //assert(is_proper_desc k2 k');
    
    (* since Root -> k' path exists, k' -> k2 edge exists, Root -> k2 path exists *)
    //assert(points_to pf k2 k');
    lemma_points_to_reachable pf k2 k';
    lemma_reachable_transitive pf k2 k' Root;
    //assert(BP.root_reachable pf k2);

    (* k' points to k2 and k is a descendant of k2 *)
    if is_desc k k2 then

      (* if k = k2, we have a contradiction since k is root_reachable *)
      if k = k2 then ()

      (* if k2 <> k, then k2 is a proper ancestor of k, which is a contradiction since k' is the 
       * first such ancestor going up from k *)
      else 
        //assert(is_proper_desc k k2);        
        lemma_proving_ancestor_greatest_depth itsl k k2
        //assert(depth k2 <= depth k');
      
    (* nothing to prove if k is not a descendant of k2 *)
    else ()

(* when evicted as merkle the proving ancestor contains our hash *)
let lemma_proving_ancestor_has_hash (itsl: TL.eac_log) (k:key{k<> Root}):
  Lemma (requires (is_eac_state_evicted_merkle itsl k))
        (ensures (mv_pointed_hash (eac_merkle_value itsl (proving_ancestor itsl k))
                                  (desc_dir k (proving_ancestor itsl k)) = 
                  hashfn (eac_value itsl k))) = 
  admit()                  

(* when evicted as blum the proving ancestor contains a bit indicating the eviction *)
let lemma_proving_ancestor_blum_bit (itsl: TL.eac_log) (k:key{k <> Root}):
  Lemma (requires (TL.is_eac_state_evicted itsl k))
        (ensures (mv_evicted_to_blum (eac_merkle_value itsl (proving_ancestor itsl k))
                                     (desc_dir k (proving_ancestor itsl k)) = 
                  is_eac_state_evicted_blum itsl k)) = admit()

(* if a key is the store of any verifier, then it is root reachable *)
let lemma_instore_implies_root_reachable (itsl: TL.eac_log) (k:key) (tid:valid_tid itsl):
  Lemma (requires (store_contains (TL.thread_store itsl tid) k))
        (ensures (root_reachable itsl k)) = admit()

(* 
 * Helper lemma for lemma_addm_ancestor_is_proving 
 *
 * the last log entry is AddM (k,_) k' such that k is root_reachable and 
 * eac_value of k' along the direction of k is emtpy. 
 * We prove that this produces a contradiction.
 *)
let lemma_addm_ancestor_is_proving_caseA (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   let itsl' = I.prefix itsl (n - 1) in
                   let k = V.key_of e in
                   TL.is_eac itsl' /\
                   Root <> k /\
                   root_reachable itsl' k /\
                   AddM? e /\
                   (let k' = AddM?.k' e in
                    let v' = eac_merkle_value itsl' k' in
                     is_proper_desc k k' /\
                     (let d = desc_dir k k' in
                       mv_points_to_none v' d))))
        (ensures False) =
  let n = I.length itsl in
  let e = I.index itsl (n - 1) in
  let itsl' = I.prefix itsl (n - 1) in
  let k = V.key_of e in
  let k' = AddM?.k' e in
  let pk = proving_ancestor itsl' k in
  let pf = eac_ptrfn itsl' in

  let tid = TL.thread_id_of itsl (n - 1) in

  (* state of verifier thread tid after processing itsl *)
  let vs = thread_state_post itsl (n - 1) in

  (* state of verifier thread tid before processing e *)
  let vs' = thread_state_pre itsl (n - 1) in

  (* store of verifier thread tid before processing e *)
  let st' = thread_store itsl' tid in

  lemma_verifier_thread_state_extend itsl (n - 1);
  //assert(s == t_verify_step s' e);

  (* k' is in the verifier store since vaddm checks this *)
  //assert(store_contains st' k');

  let v' = to_merkle_value (V.stored_value st' k') in
  let d = desc_dir k k' in
  //let dh' = desc_hash_dir v' d in

  lemma_eac_value_is_stored_value itsl' k' tid;
  //assert(v' = eac_merkle_value itsl' k');
  //assert(dh' = Empty);

  lemma_instore_implies_root_reachable itsl' k' tid;
  //assert(root_reachable itsl' k');

  lemma_reachable_between pf k k'

let lemma_addm_ancestor_is_proving_caseB (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   let itsl' = I.prefix itsl (n - 1) in
                   let k = V.key_of e in
                   TL.is_eac itsl' /\
                   Root <> k /\
                   root_reachable itsl' k /\
                   AddM? e /\
                   (let k' = AddM?.k' e in
                    let v' = eac_merkle_value itsl' k' in
                     is_proper_desc k k' /\
                     (let d = desc_dir k k' in
                       mv_points_to v' d k))))
        (ensures (let n = I.length itsl in
                  let e = I.index itsl (n - 1) in
                  let itsl' = I.prefix itsl (n - 1) in
                  let k = V.key_of e in
                  AddM?.k' e = proving_ancestor itsl' k)) = 
  let n = I.length itsl in
  let e = I.index itsl (n - 1) in
  let itsl' = I.prefix itsl (n - 1) in
  let k = V.key_of e in
  let k' = AddM?.k' e in
  let pk = proving_ancestor itsl' k in
  let pf = eac_ptrfn itsl' in

  let tid = TL.thread_id_of itsl (n - 1) in

  (* state of verifier thread tid after processing itsl *)
  let vs = thread_state_post itsl (n - 1) in

  (* state of verifier thread tid before processing e *)
  let vs' = thread_state_pre itsl (n - 1) in

  (* store of verifier thread tid before processing e *)
  let st' = thread_store itsl' tid in

  lemma_verifier_thread_state_extend itsl (n - 1);
  //assert(s == t_verify_step s' e);

  (* k' is in the verifier store since vaddm checks this *)
  //assert(store_contains st' k');

  let v' = to_merkle_value (V.stored_value st' k') in
  let d = desc_dir k k' in
  let dh' = desc_hash_dir v' d in

  lemma_eac_value_is_stored_value itsl' k' tid;
  //assert(v' = eac_merkle_value itsl' k');
  //assert(mv_points_to v' d k);

  lemma_eac_ptrfn itsl' k' d;
  //assert(points_to pf k k');

  lemma_instore_implies_root_reachable itsl' k' tid;
  lemma_points_to_is_prev pf k Root k';

  //assert(prev_in_path pf k Root = k');
  ()

let lemma_addm_ancestor_is_proving_caseC (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   let itsl' = I.prefix itsl (n - 1) in
                   let k = V.key_of e in
                   TL.is_eac itsl' /\
                   Root <> k /\
                   root_reachable itsl' k /\
                   AddM? e /\
                   (let k' = AddM?.k' e in
                    let v' = eac_merkle_value itsl' k' in
                     is_proper_desc k k' /\
                     (let d = desc_dir k k' in
                       mv_points_to_some v' d &&
                       not (mv_points_to v' d k)))))
        (ensures False) =
  let n = I.length itsl in
  let e = I.index itsl (n - 1) in
  let itsl' = I.prefix itsl (n - 1) in
  let k = V.key_of e in
  let k' = AddM?.k' e in
  let pk = proving_ancestor itsl' k in
  let pf = eac_ptrfn itsl' in

  let tid = TL.thread_id_of itsl (n - 1) in

  (* state of verifier thread tid after processing itsl *)
  let vs = thread_state_post itsl (n - 1) in

  (* state of verifier thread tid before processing e *)
  let vs' = thread_state_pre itsl (n - 1) in

  (* store of verifier thread tid before processing e *)
  let st' = thread_store itsl' tid in

  lemma_verifier_thread_state_extend itsl (n - 1);
  //assert(s == t_verify_step s' e);

  (* k' is in the verifier store since vaddm checks this *)
  //assert(store_contains st' k');

  let v' = to_merkle_value (V.stored_value st' k') in
  let d = desc_dir k k' in
  let dh' = desc_hash_dir v' d in

  lemma_eac_value_is_stored_value itsl' k' tid;
  //assert(v' = eac_merkle_value itsl' k');                    

  lemma_eac_ptrfn itsl' k' d;
  lemma_instore_implies_root_reachable itsl' k' tid;

  match dh' with
  | Desc k2 _ _ ->
    //assert(k2 <> k);
    //assert(is_proper_desc k2 k);
    lemma_proper_desc_depth_monotonic k2 k;
    
    //lemma_proper_desc_transitive1 k2 k k';
    //assert(points_to pf k2 k');
    lemma_reachable_between pf k k';
    //assert(is_desc k k2);
    lemma_desc_depth_monotonic k k2

let lemma_addm_ancestor_is_proving_caseD (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   let itsl' = I.prefix itsl (n - 1) in
                   let k = V.key_of e in
                   TL.is_eac itsl' /\
                   Root <> k /\
                   not (root_reachable itsl' k) /\
                   AddM? e /\
                   (let k' = AddM?.k' e in
                    let v' = eac_merkle_value itsl' k' in
                     is_proper_desc k k' /\
                     (let d = desc_dir k k' in
                       mv_points_to_none v' d))))
        (ensures (let n = I.length itsl in
                  let e = I.index itsl (n - 1) in
                  let itsl' = I.prefix itsl (n - 1) in
                  let k = V.key_of e in
                  AddM?.k' e = proving_ancestor itsl' k)) = 
  let n = I.length itsl in
  let e = I.index itsl (n - 1) in
  let itsl' = I.prefix itsl (n - 1) in
  let k = V.key_of e in
  let k' = AddM?.k' e in
  let pk = proving_ancestor itsl' k in
  let pf = eac_ptrfn itsl' in

  let tid = TL.thread_id_of itsl (n - 1) in

  (* state of verifier thread tid after processing itsl *)
  let vs = thread_state_post itsl (n - 1) in

  (* state of verifier thread tid before processing e *)
  let vs' = thread_state_pre itsl (n - 1) in

  (* store of verifier thread tid before processing e *)
  let st' = thread_store itsl' tid in

  lemma_verifier_thread_state_extend itsl (n - 1);
  //assert(s == t_verify_step s' e);

  (* k' is in the verifier store since vaddm checks this *)
  //assert(store_contains st' k');

  let v' = to_merkle_value (V.stored_value st' k') in
  let d = desc_dir k k' in
  let dh' = desc_hash_dir v' d in

  lemma_eac_value_is_stored_value itsl' k' tid;
  //assert(v' = eac_merkle_value itsl' k');                    

  lemma_instore_implies_root_reachable itsl' k' tid;
  lemma_proving_ancestor_greatest_depth itsl' k k';
  //assert(depth k' <= depth pk);

  lemma_eac_ptrfn itsl' k' d;

  if pk = k' then ()
  else (
    lemma_two_ancestors_related k k' pk;

    if is_desc pk k' then (
      //assert(BP.root_reachable pf pk);
      //assert(is_proper_desc pk k');
      //assert(BP.root_reachable pf k');
      lemma_reachable_between pf pk k';
      //assert(points_to_some pf k' (desc_dir pk k'));
      lemma_two_ancestors_related k pk (child d k');
  
      if is_desc pk (child d k') then ()
      else (
        //assert(is_proper_desc (child d k') pk);
        lemma_proper_desc_depth_monotonic pk k';
        lemma_proper_desc_depth_monotonic (child d k') pk
      )
    )
    else 
      //assert(is_proper_desc k' pk);
      lemma_proper_desc_depth_monotonic k' pk
    
  )

let lemma_addm_ancestor_is_proving_caseE (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   let itsl' = I.prefix itsl (n - 1) in
                   let k = V.key_of e in
                   TL.is_eac itsl' /\
                   Root <> k /\
                   not (root_reachable itsl' k) /\
                   AddM? e /\
                   (let k' = AddM?.k' e in
                    let v' = eac_merkle_value itsl' k' in
                     is_proper_desc k k' /\
                     (let d = desc_dir k k' in
                       mv_points_to v' d k))))
        (ensures False) = 
  let n = I.length itsl in
  let e = I.index itsl (n - 1) in
  let itsl' = I.prefix itsl (n - 1) in
  let k = V.key_of e in
  let k' = AddM?.k' e in
  let pk = proving_ancestor itsl' k in
  let pf = eac_ptrfn itsl' in

  let tid = TL.thread_id_of itsl (n - 1) in

  (* state of verifier thread tid after processing itsl *)
  let vs = thread_state_post itsl (n - 1) in

  (* state of verifier thread tid before processing e *)
  let vs' = thread_state_pre itsl (n - 1) in

  (* store of verifier thread tid before processing e *)
  let st' = thread_store itsl' tid in

  lemma_verifier_thread_state_extend itsl (n - 1);
  //assert(s == t_verify_step s' e);

  (* k' is in the verifier store since vaddm checks this *)
  //assert(store_contains st' k');

  let v' = to_merkle_value (V.stored_value st' k') in
  let d = desc_dir k k' in
  let dh' = desc_hash_dir v' d in

  lemma_eac_value_is_stored_value itsl' k' tid;
  //assert(v' = eac_merkle_value itsl' k');

  lemma_instore_implies_root_reachable itsl' k' tid;
  //assert(root_reachable itsl' k');

  lemma_eac_ptrfn itsl' k' d;
  //assert(points_to pf k k');
  lemma_points_to_reachable pf k k';
  lemma_reachable_transitive pf k k' Root;  
  ()

let lemma_addm_ancestor_is_proving_caseF (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   let itsl' = I.prefix itsl (n - 1) in
                   let k = V.key_of e in
                   TL.is_eac itsl' /\
                   Root <> k /\
                   not (root_reachable itsl' k) /\
                   AddM? e /\
                   (let k' = AddM?.k' e in
                    let v' = eac_merkle_value itsl' k' in
                     is_proper_desc k k' /\
                     (let d = desc_dir k k' in
                       mv_points_to_some v' d &&
                       not (mv_points_to v' d k)))))
        (ensures (let n = I.length itsl in
                  let e = I.index itsl (n - 1) in
                  let itsl' = I.prefix itsl (n - 1) in
                  let k = V.key_of e in
                  AddM?.k' e = proving_ancestor itsl' k)) =                        
  let n = I.length itsl in
  let e = I.index itsl (n - 1) in
  let itsl' = I.prefix itsl (n - 1) in
  let k = V.key_of e in
  let k' = AddM?.k' e in
  let pk = proving_ancestor itsl' k in
  let pf = eac_ptrfn itsl' in

  let tid = TL.thread_id_of itsl (n - 1) in

  (* state of verifier thread tid after processing itsl *)
  let vs = thread_state_post itsl (n - 1) in

  (* state of verifier thread tid before processing e *)
  let vs' = thread_state_pre itsl (n - 1) in

  (* store of verifier thread tid before processing e *)
  let st' = thread_store itsl' tid in

  lemma_verifier_thread_state_extend itsl (n - 1);
  //assert(s == t_verify_step s' e);

  (* k' is in the verifier store since vaddm checks this *)
  //assert(store_contains st' k');

  let v' = to_merkle_value (V.stored_value st' k') in
  let d = desc_dir k k' in
  let dh' = desc_hash_dir v' d in

  lemma_eac_value_is_stored_value itsl' k' tid;
  //assert(v' = eac_merkle_value itsl' k');                    

  lemma_eac_ptrfn itsl' k' d;
  lemma_instore_implies_root_reachable itsl' k' tid;

  lemma_proving_ancestor_greatest_depth itsl' k k';
  assert(depth k' <= depth pk);

  match dh' with
  | Desc k2 _ _ ->
    assert(k2 <> k);
    assert(is_proper_desc k2 k);

    if pk = k' then ()
    else (
      lemma_two_ancestors_related k k' pk;

      if is_desc k' pk then 
        lemma_proper_desc_depth_monotonic k' pk
      else (
        lemma_reachable_between pf pk k';
        lemma_two_ancestors_related k pk (child d k');
        if is_desc pk (child d k') then (
          lemma_desc_depth_monotonic pk k2;
          lemma_proper_desc_depth_monotonic k pk;
          lemma_proper_desc_depth_monotonic k2 k
        )
        else (
          lemma_proper_desc_depth_monotonic pk k';
          lemma_proper_desc_depth_monotonic (child d k') pk
        )
      )
    )

let lemma_addm_ancestor_is_proving (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (TL.is_eac (I.prefix itsl (I.length itsl - 1)) /\
                   AddM? (I.index itsl (I.length itsl - 1))))
        (ensures (let n = I.length itsl in
                  let e = I.index itsl (n - 1) in
                  let itsl' = I.prefix itsl (n - 1) in
                  let k = V.key_of e in
                  Root <> k /\ AddM?.k' e = proving_ancestor itsl' k)) = 
  let n = I.length itsl in
  let e = I.index itsl (n - 1) in
  let itsl' = I.prefix itsl (n - 1) in
  let k = V.key_of e in                  
  let k' = AddM?.k' e in
  
  let tid = TL.thread_id_of itsl (n - 1) in  

  (* state of verifier thread tid after processing itsl *)
  let vs = thread_state_post itsl (n - 1) in

  (* state of verifier thread tid before processing e *)
  let vs' = thread_state_pre itsl (n - 1) in

  (* store of verifier thread tid before processing e *)
  let st' = thread_store itsl' tid in

  lemma_verifier_thread_state_extend itsl (n - 1);
  //assert(s == t_verify_step s' e);

  (* k is a proper desc of k' since verifier checks this in vaddm *)
  assert(is_proper_desc k k');

  (* so k cannot be Root *)
  assert(k <> Root);

  (* k' is in the verifier store since vaddm checks this *)
  assert(store_contains st' k');
  
  let v' = to_merkle_value (V.stored_value st' k') in
  let d = desc_dir k k' in
  let dh' = desc_hash_dir v' d in
  lemma_eac_value_is_stored_value itsl' k' tid;
  assert(v' = eac_merkle_value itsl' k');

  if root_reachable itsl' k then (
    match dh' with
    | Empty -> 
      lemma_addm_ancestor_is_proving_caseA itsl
    | Desc k2 _ _ -> 
      if k2 = k then lemma_addm_ancestor_is_proving_caseB itsl        
      else lemma_addm_ancestor_is_proving_caseC itsl
  )  
  else (
    match dh' with
    | Empty -> lemma_addm_ancestor_is_proving_caseD itsl
    | Desc k2 _ _ -> 
      if k2 = k then lemma_addm_ancestor_is_proving_caseE itsl
      else lemma_addm_ancestor_is_proving_caseF itsl
  )

(* if the store contains a k, it contains its proving ancestor *)
let lemma_store_contains_proving_ancestor (itsl: TL.eac_log) 
  (tid:TL.valid_tid itsl) (k:key{k <> Root}):
  Lemma (store_contains (TL.thread_store itsl tid) k ==>
         store_contains (TL.thread_store itsl tid)
                        (proving_ancestor itsl k)) = admit()

