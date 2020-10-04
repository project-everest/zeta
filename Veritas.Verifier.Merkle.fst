module Veritas.Verifier.Merkle

open Veritas.BinTreePtr
open Veritas.EAC
open Veritas.Interleave

module BP=Veritas.BinTreePtr
module E=Veritas.EAC

(* does the log entry update which descendant the value of k points to? *)
let updates_points_to (e: vlog_entry) (k: merkle_key): bool = 
  match e with
  | AddM (k1,_) k2 -> k1 = k || k2 = k  
  | _ -> false

let lemma_points_to_unchanged_caseA_root (itsl: TL.eac_log{I.length itsl > 0}) (c:bin_tree_dir):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   let ke = V.key_of e in
                   not (updates_points_to e Root) /\ ke <> Root))
        (ensures (let n = I.length itsl in
                  let itsl' = I.prefix itsl (n - 1) in 
                  let v = eac_merkle_value itsl Root in
                  let v' = eac_merkle_value itsl' Root in
                  mv_points_to_none v c && mv_points_to_none v' c || 
                  mv_points_to_some v c && mv_points_to_some v' c && 
                  mv_pointed_key v c = mv_pointed_key v' c)) = 
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  let e = I.index itsl (n - 1) in
  let ke = V.key_of e in

  lemma_fullprefix_equal itsl;
  lemma_root_in_store0 itsl;
  lemma_root_in_store0 itsl';

  lemma_eac_value_is_stored_value itsl' Root 0;
  lemma_eac_value_is_stored_value itsl Root 0;

  (* thread id where element e goes *)
  let tid = thread_id_of itsl (n - 1) in

  if tid = 0 then 
    lemma_verifier_thread_state_extend itsl (n - 1)  
  else
    lemma_verifier_thread_state_extend2 itsl (n - 1) 0
    
let lemma_points_to_unchanged_caseA (itsl: TL.eac_log{I.length itsl > 0}) (k:merkle_key) (c:bin_tree_dir):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   let ke = V.key_of e in
                   not (updates_points_to e k) /\ ke <> k ))
        (ensures (let n = I.length itsl in
                  let itsl' = I.prefix itsl (n - 1) in 
                  let v = eac_merkle_value itsl k in
                  let v' = eac_merkle_value itsl' k in
                  mv_points_to_none v c && mv_points_to_none v' c || 
                  mv_points_to_some v c && mv_points_to_some v' c && 
                  mv_pointed_key v c = mv_pointed_key v' c)) = 
   if k = Root then lemma_points_to_unchanged_caseA_root itsl c
   else

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

     if tid = tidk then (
       lemma_verifier_thread_state_extend itsl (n - 1);
       assert(TL.thread_state itsl tid == t_verify_step (TL.thread_state itsl' tid) e);

       lemma_eac_value_is_stored_value itsl k tid;
       lemma_eac_value_is_stored_value itsl' k tid
     )
     else (
       (* the thread state of tidk does not change after processing element e *)
       lemma_verifier_thread_state_extend2 itsl (n - 1) tidk;
       //assert(TL.thread_store itsl' tidk == TL.thread_store itsl tidk);
       lemma_eac_value_is_stored_value itsl k tidk;
       //assert(eac_value itsl k = V.stored_value (TL.thread_store itsl tidk) k);
       lemma_eac_value_is_stored_value itsl' k tidk
     )
       
   | EACEvictedMerkle _
   | EACEvictedBlum _ _ _ ->    
     lemma_eac_value_is_evicted_value itsl k;
     lemma_eac_value_is_evicted_value itsl' k;     
     ()

let lemma_points_to_unchanged_evictm (itsl: TL.eac_log {I.length itsl > 0 }) (k: merkle_key) (c: bin_tree_dir):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   V.key_of e = k /\ EvictM? e))
        (ensures (let n = I.length itsl in
                  let itsl' = I.prefix itsl (n - 1) in 
                  let v = eac_merkle_value itsl k in
                  let v' = eac_merkle_value itsl' k in
                  mv_points_to_none v c && mv_points_to_none v' c || 
                  mv_points_to_some v c && mv_points_to_some v' c && 
                  mv_pointed_key v c = mv_pointed_key v' c)) = 
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  let e = I.index itsl (n - 1) in
  let ee = TL.vlog_entry_ext_at itsl (n - 1) in
  let tid = TL.thread_id_of itsl (n - 1) in
  let vs = TL.thread_state itsl tid in
  let vs' = TL.thread_state itsl' tid in

  lemma_fullprefix_equal itsl;
  lemma_verifier_thread_state_extend itsl (n - 1);
  // assert(vs == t_verify_step vs' e);

  let es' = TL.eac_state_of_key itsl' k in
  let es = TL.eac_state_of_key itsl k in
  lemma_eac_state_transition itsl (n - 1);
  // assert(es = eac_add ee es');

  (* thread store before processing e *)
  let st' = TL.thread_store itsl' tid in

  match e with
  | EvictM _ k' ->
    (* verifier checks store contains k when processing e *)
    //assert(store_contains st' k);

    (* verifier does not allow evicting the root *)
    //assert(k <> Root);

    (* es' is EACInStore *)
    lemma_instore_implies_eac_state_instore itsl' k tid;
    //assert(E.EACInStore? es');

    (* since we go from es' -> es, this implies es is EACEvictedmerkle *)
    lemma_eac_state_of_key_valid itsl k;
    //assert(E.EACEvictedMerkle? es);
    //assert(E.EACEvictedMerkle?.v es = value_ext ee);

    (* value recorded in es is V.stored_value st' k *)
    lemma_ext_evict_val_is_stored_val itsl (n - 1);
    //assert(V.stored_value st' k = value_ext ee);

    lemma_eac_value_is_evicted_value itsl k;
    //assert(eac_value itsl k = value_ext ee);

    lemma_eac_value_is_stored_value itsl' k tid;
    //assert(eac_value itsl' k = V.stored_value st' k);
    
    ()

let lemma_points_to_unchanged_addb (itsl: TL.eac_log {I.length itsl > 0 }) (k: merkle_key) (c: bin_tree_dir):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   V.key_of e = k /\ AddB? e))
        (ensures (let n = I.length itsl in
                  let itsl' = I.prefix itsl (n - 1) in 
                  let v = eac_merkle_value itsl k in
                  let v' = eac_merkle_value itsl' k in
                  mv_points_to_none v c && mv_points_to_none v' c || 
                  mv_points_to_some v c && mv_points_to_some v' c && 
                  mv_pointed_key v c = mv_pointed_key v' c)) = 
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  let e = I.index itsl (n - 1) in
  let ee = TL.vlog_entry_ext_at itsl (n - 1) in
  let tid = TL.thread_id_of itsl (n - 1) in
  let vs = TL.thread_state itsl tid in
  let vs' = TL.thread_state itsl' tid in

  lemma_fullprefix_equal itsl;
  lemma_verifier_thread_state_extend itsl (n - 1);
  // assert(vs == t_verify_step vs' e);

  let es' = TL.eac_state_of_key itsl' k in
  let es = TL.eac_state_of_key itsl k in
  lemma_eac_state_transition itsl (n - 1);
  // assert(es = eac_add ee es');

  (* both es and es' are non-fail states *)
  lemma_eac_state_of_key_valid itsl k;
  lemma_eac_state_of_key_valid itsl' k;
  // assert(es <> EACFail && es' <> EACFail);  

  (* thread store after processing e *)
  let st = TL.thread_store itsl tid in

  match e with
  | AddB (_,v) _ _ ->
    
    (* the store contains k after the add *)
    // assert(V.store_contains st k);

    (* the only possibility for es'; EACInit, EACInStore, EACEvictedMerkle do not allow AddB *)
    // assert(EACEvictedBlum? es');

    (* the eac_value of k before e is the evict_state value *)
    lemma_eac_value_is_evicted_value itsl' k;
    //assert(eac_value itsl' k = EACEvictedBlum?.v es');

    (* eac implies the added value is the value in es' *)
    // assert(v = EACEvictedBlum?.v es');
    
    (* the added value is the value in the store *)
    // assert(V.stored_value st k = v);

    (* the eac_value of k after e is the stored value *)
    lemma_eac_value_is_stored_value itsl k tid;
    // assert(eac_value itsl k = V.stored_value st k);

    (* all previous equalities imply eac_value of k is the same before and after e *)
    // assert(eac_value itsl k = eac_value itsl' k);

    ()                  

let lemma_points_to_unchanged_evictb (itsl: TL.eac_log {I.length itsl > 0 }) (k: merkle_key) (c: bin_tree_dir):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   V.key_of e = k /\ EvictB? e))
        (ensures (let n = I.length itsl in
                  let itsl' = I.prefix itsl (n - 1) in 
                  let v = eac_merkle_value itsl k in
                  let v' = eac_merkle_value itsl' k in
                  mv_points_to_none v c && mv_points_to_none v' c || 
                  mv_points_to_some v c && mv_points_to_some v' c && 
                  mv_pointed_key v c = mv_pointed_key v' c)) = 
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  let e = I.index itsl (n - 1) in
  let ee = TL.vlog_entry_ext_at itsl (n - 1) in
  let tid = TL.thread_id_of itsl (n - 1) in
  let vs = TL.thread_state itsl tid in
  let vs' = TL.thread_state itsl' tid in

  lemma_fullprefix_equal itsl;
  lemma_verifier_thread_state_extend itsl (n - 1);
  // assert(vs == t_verify_step vs' e);

  let es' = TL.eac_state_of_key itsl' k in
  let es = TL.eac_state_of_key itsl k in
  lemma_eac_state_transition itsl (n - 1);
  // assert(es = eac_add ee es');

  (* both es and es' are non-fail states *)
  lemma_eac_state_of_key_valid itsl k;
  lemma_eac_state_of_key_valid itsl' k;
  // assert(es <> EACFail && es' <> EACFail);  

  (* thread store before processing e *)
  let st' = TL.thread_store itsl' tid in

  match e with
  | EvictB _ _ ->

    (* the verifier checks that store contains k before evicting *)
    // assert(V.store_contains st' k);

    (* the eac_value is stored value *)
    lemma_eac_value_is_stored_value itsl' k tid;
    // assert(eac_value itsl' k = V.stored_value st' k);

    (* since k is in st', its EAC state is EACInStore *)
    lemma_instore_implies_eac_state_instore itsl' k tid;
    // assert(EACInStore? es');
    // assert(EACEvictedBlum? es);

    (* the value recorded in extended e (ee) is the stored value *)
    lemma_ext_evict_val_is_stored_val itsl (n - 1);
    // assert(value_ext ee = V.stored_value st' k);

    (* the value in the EAC state es is the value from ee *)
    // assert(EACEvictedBlum?.v es = value_ext ee);

    (* the eac_value of k after processing e is the value in EAC state es *)
    lemma_eac_value_is_evicted_value itsl k;
    // assert(eac_value itsl k = EACEvictedBlum?.v es);

    (* the previous equalities imply, the eac_value of k remains unchanged when processing e *)
    // assert(eac_value itsl k = eac_value itsl' k);

    ()                 

let lemma_points_to_unchanged_evictbm (itsl: TL.eac_log {I.length itsl > 0 }) (k: merkle_key) (c: bin_tree_dir):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   V.key_of e = k /\ EvictBM? e))
        (ensures (let n = I.length itsl in
                  let itsl' = I.prefix itsl (n - 1) in 
                  let v = eac_merkle_value itsl k in
                  let v' = eac_merkle_value itsl' k in
                  mv_points_to_none v c && mv_points_to_none v' c || 
                  mv_points_to_some v c && mv_points_to_some v' c && 
                  mv_pointed_key v c = mv_pointed_key v' c)) = 
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  let e = I.index itsl (n - 1) in
  let ee = TL.vlog_entry_ext_at itsl (n - 1) in
  let tid = TL.thread_id_of itsl (n - 1) in
  let vs = TL.thread_state itsl tid in
  let vs' = TL.thread_state itsl' tid in

  lemma_fullprefix_equal itsl;
  lemma_verifier_thread_state_extend itsl (n - 1);
  // assert(vs == t_verify_step vs' e);

  let es' = TL.eac_state_of_key itsl' k in
  let es = TL.eac_state_of_key itsl k in
  lemma_eac_state_transition itsl (n - 1);
  // assert(es = eac_add ee es');

  (* both es and es' are non-fail states *)
  lemma_eac_state_of_key_valid itsl k;
  lemma_eac_state_of_key_valid itsl' k;
  // assert(es <> EACFail && es' <> EACFail);  

  (* thread store before processing e *)
  let st' = TL.thread_store itsl' tid in

  match e with
  | EvictBM _ _ _ ->

    (* the verifier checks that store contains k before evicting *)
    assert(V.store_contains st' k);

    (* the eac_value is stored value *)
    lemma_eac_value_is_stored_value itsl' k tid;
    assert(eac_value itsl' k = V.stored_value st' k);

    (* since k is in st', its EAC state is EACInStore *)
    lemma_instore_implies_eac_state_instore itsl' k tid;
    assert(EACInStore? es');
    assert(EACEvictedBlum? es);

    (* the value recorded in extended e (ee) is the stored value *)
    lemma_ext_evict_val_is_stored_val itsl (n - 1);
    // assert(value_ext ee = V.stored_value st' k);

    (* the value in the EAC state es is the value from ee *)
    // assert(EACEvictedBlum?.v es = value_ext ee);

    (* the eac_value of k after processing e is the value in EAC state es *)
    lemma_eac_value_is_evicted_value itsl k;
    // assert(eac_value itsl k = EACEvictedBlum?.v es);

    (* the previous equalities imply, the eac_value of k remains unchanged when processing e *)
    // assert(eac_value itsl k = eac_value itsl' k);

    ()

(* A log entry not referencing key k does not affect the eac_value of k *)
let lemma_points_to_unchanged (itsl: TL.eac_log{I.length itsl > 0}) (k:merkle_key) (c:bin_tree_dir):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   not (updates_points_to e k)))
        (ensures (let n = I.length itsl in
                  let itsl' = I.prefix itsl (n - 1) in 
                  let v = eac_merkle_value itsl k in
                  let v' = eac_merkle_value itsl' k in
                  mv_points_to_none v c && mv_points_to_none v' c || 
                  mv_points_to_some v c && mv_points_to_some v' c && 
                  mv_pointed_key v c = mv_pointed_key v' c)) = 
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  let e = I.index itsl (n - 1) in
  let ke = V.key_of e in

  if ke <> k then
    lemma_points_to_unchanged_caseA itsl k c
  else ( 
    match e with
    | Get _ _ -> ()                 (* k is a merkle key *)
    | Put _ _ -> ()                 (* k is a merkle key *)
    | AddM _ _ -> ()                 (* update_points_to ... => contradiction *)
    | EvictM _ _ -> lemma_points_to_unchanged_evictm itsl k c
    | AddB _ _ _ -> lemma_points_to_unchanged_addb itsl k c
    | EvictB _ _ -> lemma_points_to_unchanged_evictb itsl k c    
    | EvictBM _ _ _ -> lemma_points_to_unchanged_evictbm itsl k c
  )

let lemma_eac_value_empty_or_points_to_desc_addmA
  (itsl: TL.eac_log {I.length itsl > 0})
  (k:merkle_key)
  (c:bin_tree_dir):
  Lemma (requires (let n = I.length itsl in
                   let itsl' = I.prefix itsl (n - 1) in
                   let e = I.index itsl (n - 1) in                   
                   let v' = eac_merkle_value itsl' k in
                   V.key_of e = k /\ AddM? e /\
                   (mv_points_to_none v' c \/
                    mv_points_to_some v' c /\ is_desc (mv_pointed_key v' c) (child c k))))
         (ensures (let v = eac_merkle_value itsl k in
                   mv_points_to_none v c \/
                   mv_points_to_some v c /\ is_desc (mv_pointed_key v c) (child c k))) = 
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  let e = I.index itsl (n - 1) in
  let ee = TL.vlog_entry_ext_at itsl (n - 1) in
  let tid = TL.thread_id_of itsl (n - 1) in
  let vs = TL.thread_state itsl tid in
  let vs' = TL.thread_state itsl' tid in

  lemma_fullprefix_equal itsl;
  lemma_verifier_thread_state_extend itsl (n - 1);
  // assert(vs == t_verify_step vs' e);

  let es' = TL.eac_state_of_key itsl' k in
  let es = TL.eac_state_of_key itsl k in
  lemma_eac_state_transition itsl (n - 1);
  // assert(es = eac_add ee es');

  (* both es and es' are non-fail states *)
  lemma_eac_state_of_key_valid itsl k;
  lemma_eac_state_of_key_valid itsl' k;
  // assert(es <> EACFail && es' <> EACFail);  

  (* thread store before processing e *)
  let st' = TL.thread_store itsl' tid in
  (* thread store after processing e *)
  let st = TL.thread_store itsl tid in
  match e with
  | AddM (_,v) k' ->
    (* verifier checks *)
    // assert(is_proper_desc k k');
    // assert(V.store_contains st' k');
    // assert(is_value_of k v);

    let v' = to_merkle_value (V.stored_value st' k') in
    let c' = desc_dir k k' in
    let dh' = desc_hash_dir v' c' in
    match dh' with
    | Empty -> 
      // assert(v = init_value k);
      // assert(V.store_contains st k);      
      // assert(V.stored_value st k = v);
      lemma_eac_value_is_stored_value itsl k tid
      
    | Desc k2 _ _ ->
      if k2 = k then (
        // assert(V.stored_value st k = v);        
        lemma_eac_value_is_stored_value itsl k tid;
        // assert(eac_value itsl k = v);

        if init_value k = v then ()       (* value points to none *)
        else (
          // assert(EACEvictedMerkle? es');
          lemma_eac_value_is_evicted_value itsl' k;
          // assert(eac_value itsl' k = EACEvictedMerkle?.v es');
          // assert(EACEvictedMerkle?.v es' = v);
          // assert(eac_value itsl' k = eac_value itsl k);

          ()
        )
      )
      else 
        //assert(v = init_value k);
        //assert(is_proper_desc k2 k);
        lemma_eac_value_is_stored_value itsl k tid
      
let lemma_eac_value_empty_or_points_to_desc_addmB
  (itsl: TL.eac_log {I.length itsl > 0})
  (k:merkle_key)
  (c:bin_tree_dir):
  Lemma (requires (let n = I.length itsl in
                   let itsl' = I.prefix itsl (n - 1) in
                   let e = I.index itsl (n - 1) in                   
                   let v' = eac_merkle_value itsl' k in
                   AddM? e /\ AddM?.k' e  = k /\
                   (mv_points_to_none v' c \/
                    mv_points_to_some v' c /\ is_desc (mv_pointed_key v' c) (child c k))))
         (ensures (let v = eac_merkle_value itsl k in
                   mv_points_to_none v c \/
                   mv_points_to_some v c /\ is_desc (mv_pointed_key v c) (child c k))) = 
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  let e = I.index itsl (n - 1) in
  let ee = TL.vlog_entry_ext_at itsl (n - 1) in
  let tid = TL.thread_id_of itsl (n - 1) in
  let vs = TL.thread_state itsl tid in
  let vs' = TL.thread_state itsl' tid in

  lemma_fullprefix_equal itsl;
  lemma_verifier_thread_state_extend itsl (n - 1);
  // assert(vs == t_verify_step vs' e);

  let es' = TL.eac_state_of_key itsl' k in
  let es = TL.eac_state_of_key itsl k in
  lemma_eac_state_transition itsl (n - 1);
  // assert(es = eac_add ee es');

  (* both es and es' are non-fail states *)
  lemma_eac_state_of_key_valid itsl k;
  lemma_eac_state_of_key_valid itsl' k;
  // assert(es <> EACFail && es' <> EACFail);  

  (* thread store before processing e *)
  // let st' = TL.thread_store itsl' tid in
  (* thread store after processing e *)
  // let st = TL.thread_store itsl tid in
  match e with
  | AddM (k1,v1) _ ->                     
    (* verifier checks *)
    // assert(is_proper_desc k1 k);
    // assert(V.store_contains st' k);
    // let v' = to_merkle_value (V.stored_value st' k) in
    // let c' = desc_dir k1 k in
    // let dh' = desc_hash_dir v' c' in
    // let h1 = hashfn v1 in
  
    (* store contains k after processing e *)
    // assert(V.store_contains st k);
    lemma_eac_value_is_stored_value itsl k tid;
    lemma_eac_value_is_stored_value itsl' k tid

(* for a merkle key k, the eac_value along direction c is either empty or points to a descendant *)
let rec lemma_eac_value_empty_or_points_to_desc
  (itsl: TL.eac_log)
  (k:merkle_key)
  (c:bin_tree_dir):
  Lemma (requires True)
        (ensures (let v = eac_merkle_value itsl k in
                  mv_points_to_none v c \/
                  mv_points_to_some v c /\ is_desc (mv_pointed_key v c) (child c k)))
        (decreases (I.length itsl)) = 
  let n = I.length itsl in

  if n = 0 then (
    lemma_init_state_empty itsl k;

    if k = Root then
      lemma_eac_value_root_init itsl k
    else
      lemma_eac_value_init itsl k
  )
  else 
    let itsl' = I.prefix itsl (n - 1) in
    let e = I.index itsl (n - 1) in

    lemma_eac_value_empty_or_points_to_desc itsl' k c;

    if updates_points_to e k then (
      match e with
      | AddM (k1,_) k2 ->
        (* otherwise, update_points_to is false *)
        assert(k1 = k || k2 = k);


        if k1 = k then           
          lemma_eac_value_empty_or_points_to_desc_addmA itsl k c        
        else
          lemma_eac_value_empty_or_points_to_desc_addmB itsl k c
    )
    else 
      lemma_points_to_unchanged itsl k c
      
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

(* only merkle adds may change the pointer function *)
let may_change_ptrfn (e: vlog_entry): bool = 
  match e with
  | AddM _ _ -> true
  | _ -> false

let lemma_ptrfn_unchanged_aux (itsl: TL.eac_log {I.length itsl > 0}) (k:merkle_key) (c:bin_tree_dir):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   not (may_change_ptrfn e)))
        (ensures (let n = I.length itsl in
                  let itsl' = I.prefix itsl (n - 1) in        
                  eac_ptrfn itsl k c = eac_ptrfn itsl' k c)) 
        [SMTPat (eac_ptrfn itsl k c)] =                  
  lemma_points_to_unchanged itsl k c;
  lemma_eac_ptrfn itsl k c

let lemma_ptrfn_unchanged (itsl: TL.eac_log {I.length itsl > 0}):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   not (may_change_ptrfn e)))
        (ensures (let n = I.length itsl in
                  let itsl' = I.prefix itsl (n - 1) in
                  feq_ptrfn (eac_ptrfn itsl) (eac_ptrfn itsl'))) =                     
  ()

let lemma_ptrfn_unchanged_implies_initness_unchanged (itsl: TL.eac_log {I.length itsl > 0}) (k:key {k <> Root}):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   let itsl' = I.prefix itsl (n - 1) in
                   not (may_change_ptrfn e)))
         (ensures (let n = I.length itsl in
                   let itsl' = I.prefix itsl (n - 1) in
                   is_eac_state_init itsl' k = is_eac_state_init itsl k)) = 
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in                   
  let es' = TL.eac_state_of_key itsl' k in
  let es = TL.eac_state_of_key itsl k in
  
  lemma_eac_state_of_key_valid itsl k;
  lemma_eac_state_of_key_valid itsl' k;
  assert(es <> EACFail && es' <> EACFail);  

  (* nothing to prove if es and es' are equal *)
  if es = es' then ()

  else if es = EACInit then (
    (* since es is EACInit, there is no entry of key k in itsl *)
    lemma_eac_state_init_no_entry itsl k;
    assert(not (has_some_entry_of_key itsl k));

    (* since es' is not EACInit, there is a previous add of k in itsl', which provides a contradiction *)
    lemma_eac_state_active_implies_prev_add itsl' k;
    assert(has_some_add_of_key itsl' k);

    (* the index of the last add *)
    let i = last_index (is_add_of_key k) (I.i_seq itsl') in
    lemma_last_index_correct2 (is_entry_of_key k) (I.i_seq itsl) i
  )
  else 
    admit()

let lemma_not_init_equiv_root_reachable_extend_ptrfn_unchanged (itsl: TL.eac_log {I.length itsl > 0}) (k:key {k <> Root}):
  Lemma (requires (let n = I.length itsl in
                   let e = I.index itsl (n - 1) in
                   let itsl' = I.prefix itsl (n - 1) in
                   not (may_change_ptrfn e) /\
                   (not (is_eac_state_init itsl' k) <==> root_reachable itsl' k)))                   
        (ensures (not (is_eac_state_init itsl k) <==> root_reachable itsl k)) =  
 let n = I.length itsl in
 let pf = eac_ptrfn itsl in
 let itsl' = I.prefix itsl (n - 1) in 
 let pf' = eac_ptrfn itsl' in
  
 (* the pointer functions of itsl and itsl' are the same, so root_reachability is unaffected *)        
 lemma_ptrfn_unchanged itsl;
 lemma_reachable_feq pf pf' k Root;
 assert(root_reachable itsl k = root_reachable itsl' k);

 (* since e is not AddM, the EAC initness property does not change as well *)
 lemma_ptrfn_unchanged_implies_initness_unchanged itsl k

(* a key is root reachable iff its eac_state is not EACInit *)
let rec lemma_not_init_equiv_root_reachable (itsl: TL.eac_log) (k:key{k <> Root}):
  Lemma (requires True) 
        (ensures (not (is_eac_state_init itsl k) <==> root_reachable itsl k))
        (decreases (I.length itsl)) = 
  let n = I.length itsl in
  let es = TL.eac_state_of_key itsl k in
  let pf = eac_ptrfn itsl in
  
  if n = 0 then (
    (* eac state of k is init *)
    lemma_init_state_empty itsl k;
    assert(es = EACInit);

    (* we need to prove not (root_reachable ...) *)    
    lemma_eac_value_root_init itsl Root;
    assert(eac_value itsl Root = init_value Root);
    
    (* root is a proper ancestor of k *)
    lemma_root_is_univ_ancestor k;
    assert(is_proper_desc k Root);

    (* direction of k from Root *)
    let c = desc_dir k Root in

    (* root points to None *)
    lemma_eac_ptrfn itsl Root c;
    assert(None = pf Root c);

    (* since Root points to None in direction c, k is not reachable *)
    lemma_non_reachable_desc_of_none pf k Root
  )
  else (
    let itsl' = I.prefix itsl (n - 1) in
    let e = I.index itsl (n - 1) in

    (* induction *)
    lemma_not_init_equiv_root_reachable itsl' k;


    match e with
    | AddM _ _ -> admit()
    | _ ->
      assert(not (may_change_ptrfn e));
      lemma_not_init_equiv_root_reachable_extend_ptrfn_unchanged itsl k
  )

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

