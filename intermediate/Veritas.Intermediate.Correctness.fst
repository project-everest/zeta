module Veritas.Intermediate.Correctness

open Veritas.BinTree
open Veritas.Hash
open Veritas.Key
open Veritas.MultiSet
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.SeqMachine
open Veritas.State
open Veritas.StateSeqMachine
open Veritas.Verifier
open Veritas.SeqAux
open Veritas.Verifier.EAC
open Veritas.Verifier.Merkle
open Veritas.Intermediate.Blum
open Veritas.Intermediate.Global
open Veritas.Intermediate.Logs
open Veritas.Intermediate.Store
open Veritas.Intermediate.Thread
open Veritas.Intermediate.TSLog
open Veritas.Intermediate.Verify
open Veritas.Intermediate.VerifierConfig

module E=Veritas.EAC
module I = Veritas.Interleave
module MS = Veritas.MultiSet
module S = FStar.Seq
module SA = Veritas.SeqAux
module SpecB = Veritas.Verifier.Blum
module SpecM = Veritas.Verifier.Merkle
module IntB = Veritas.Intermediate.Blum
module IntL = Veritas.Intermediate.Logs
module IntG = Veritas.Intermediate.Global
module IntV = Veritas.Intermediate.Verify
module IntS = Veritas.Intermediate.Store
module IntTS = Veritas.Intermediate.TSLog
module SpecV = Veritas.Verifier
module SpecTS = Veritas.Verifier.TSLog
module SpecC = Veritas.Verifier.Correctness

(* 
 * A bunch of properties we use in the induction step:
 *    (a) the intermediate verifiers all satisfy the store invariant
 *    (b) the intermediate and spec level verifiers states correspond to one-another (related)
 *    (c) the spec level log is time sorted (b and c imply that the spec log has type its_log)
 *    (d) the spec level log is evict-add-consistent 
 * TODO: rename this
 *)
let induction_props #vcfg (ils: its_log vcfg) = 
  let ilk = to_logk ils in
  spec_rel ils /\
  SpecTS.is_eac ilk


let induction_props_or_hash_collision #vcfg (ils: its_log vcfg) = 
  o:option hash_collision_gen{Some? o \/ induction_props ils}


let lemma_eac_boundary_inv (itsl: SpecTS.its_log) (i:I.seq_index itsl): 
  Lemma (requires (SpecTS.is_eac (I.prefix itsl i) /\
                   not (SpecTS.is_eac (I.prefix itsl (i + 1)))))
        (ensures (SpecTS.eac_boundary itsl = i)) 
        [SMTPat (I.prefix itsl i)]
        = admit()

let inductive_step_get #vcfg 
                       (ils: IntTS.hash_verifiable_log vcfg) 
                       (i:I.seq_index ils{let ils_i = I.prefix ils i in
                                              induction_props ils_i /\
                                              IntL.Get_S? (I.index ils i)}): induction_props_or_hash_collision (I.prefix ils (i + 1)) = 
  let ilk = to_logk ils in  
  let ils_i = I.prefix ils i in
  let ilk_i = I.prefix ilk i in
  let ils_i1 = I.prefix ils (i + 1) in
  let ilk_i1 = I.prefix ilk (i + 1) in  

  let vss_i = thread_state_pre ils i in
  let vsk_i = SpecTS.thread_state_pre ilk i in 
  let es = I.index ils i in
  SpecTS.lemma_verifier_thread_state_extend ilk i;
  
  match es with
  
  | Get_S s k v ->
    lemma_vget_simulates_spec vss_i vsk_i es;
    lemma_forall_vtls_rel_extend ils i;    
    lemma_vget_preserves_ismap vss_i es;
    lemma_forall_store_ismap_extend ils i;
    
    if SpecTS.is_eac ilk_i1 then
      None    
    else (
      lemma_eac_boundary_inv ilk_i1 i;
      Some (lemma_non_eac_get_implies_hash_collision ilk_i1)
    )

let inductive_step_put #vcfg 
                       (ils: IntTS.hash_verifiable_log vcfg) 
                       (i:I.seq_index ils{let ils_i = I.prefix ils i in
                                              induction_props ils_i /\
                                              IntL.Put_S? (I.index ils i)}): induction_props_or_hash_collision (I.prefix ils (i + 1)) = 
  let ilk = to_logk ils in  
  let ils_i = I.prefix ils i in
  let ilk_i = I.prefix ilk i in
  let ils_i1 = I.prefix ils (i + 1) in
  let ilk_i1 = I.prefix ilk (i + 1) in  

  let vss_i = thread_state_pre ils i in
  let vsk_i = SpecTS.thread_state_pre ilk i in 
  let es = I.index ils i in
  SpecTS.lemma_verifier_thread_state_extend ilk i;
  
  match es with
  
  | Put_S s k v -> 
    lemma_vput_simulates_spec vss_i vsk_i es;
    lemma_forall_vtls_rel_extend ils i;        
    lemma_vput_preserves_ismap vss_i es;
    lemma_forall_store_ismap_extend ils i;
    if SpecTS.is_eac ilk_i1 then
      None    
    else (
      lemma_eac_boundary_inv ilk_i1 i;
      Some (lemma_non_eac_put_implies_hash_collision ilk_i1)
    )  

let lemma_induction_props_implies_vtls_rel #vcfg
                                           (ils: its_log vcfg)
                                           (i:I.seq_index ils{induction_props (I.prefix ils i)})
  : Lemma (ensures (let ilk = IntTS.to_logk ils in
                    let vss_i = IntTS.thread_state_pre ils i in
                    let vsk_i = SpecTS.thread_state_pre ilk i in
                    vtls_rel vss_i vsk_i))
          [SMTPat (I.prefix ils i)]
  = ()                    

let inductive_step_addm_caseA #vcfg 
                              (ils: IntTS.hash_verifiable_log vcfg) 
                              (i:I.seq_index ils{let ils_i = I.prefix ils i in
                                                 let vss_i = IntTS.thread_state_pre ils i in
                                                 let sts = IntV.thread_store vss_i in
                                                 induction_props ils_i /\
                                                 AddM_S? (I.index ils i) /\                                                 
                                                 (let AddM_S s (k,v) s' = I.index ils i in
                                                  not (store_contains_key sts k))})
  : induction_props_or_hash_collision (I.prefix ils (i + 1)) = 
  let tid = IntTS.thread_id_of ils i in                                          
  let ilk = to_logk ils in  
  let ils_i = I.prefix ils i in
  let ilk_i = I.prefix ilk i in
  let ils_i1 = I.prefix ils (i + 1) in
  let ilk_i1 = I.prefix ilk (i + 1) in  
  let vss_i = thread_state_pre ils i in
  let vsk_i = SpecTS.thread_state_pre ilk i in
  let vsk_i1 = SpecTS.thread_state_post ilk i in
  let es = I.index ils i in
  SpecTS.lemma_verifier_thread_state_extend ilk i;
  
  let ek = I.index ilk i in

  match es with
  | AddM_S s (k,v) s' ->
    let sts = IntV.thread_store vss_i in
    let stk = SpecV.thread_store vsk_i in
    lemma_vaddm_preserves_spec_new_key vss_i vsk_i es;
    lemma_forall_vtls_rel_extend ils i;              
    lemma_vaddm_preserves_ismap_new_key vss_i es;
    lemma_forall_store_ismap_extend ils i;      
    if SpecTS.is_eac ilk_i1 then
      None    
    else (
      lemma_eac_boundary_inv ilk_i1 i;
      Some (lemma_non_eac_addm_implies_hash_collision ilk_i1)
    )    

let inductive_step_addm_caseB #vcfg 
                              (ils: IntTS.hash_verifiable_log vcfg)                               
                              (i:I.seq_index ils)
                              (sk: slot_id vcfg)
                              (sk_anc: slot_id vcfg{let ils_i = I.prefix ils i in
                                                    let vss_i = IntTS.thread_state_pre ils i in
                                                    let sts = IntV.thread_store vss_i in
                                                    induction_props ils_i /\
                                                    AddM_S? (I.index ils i) /\
                                                    inuse_slot sts sk /\ inuse_slot sts sk_anc /\
                                                    (let AddM_S s (k,v) s' = I.index ils i in
                                                     let k_anc = stored_key sts sk_anc in
                                                     let k' = stored_key sts s' in                                                      
                                                     stored_key sts sk = k /\ k_anc = k' /\ points_to sts sk_anc sk)})
  : induction_props_or_hash_collision (I.prefix ils (i + 1)) = 
  let tid = IntTS.thread_id_of ils i in
  let ilk = to_logk ils in  
  let ils_i = I.prefix ils i in
  let ilk_i = I.prefix ilk i in
  let ils_i1 = I.prefix ils (i + 1) in
  let ilk_i1 = I.prefix ilk (i + 1) in  
  let vss_i = thread_state_pre ils i in
  let vsk_i = SpecTS.thread_state_pre ilk i in
  let vsk_i1 = SpecTS.thread_state_post ilk i in
  let es = I.index ils i in
  SpecTS.lemma_verifier_thread_state_extend ilk i;

  let ek = I.index ilk i in

  match es with
  | AddM_S s (k,v) s' ->
    let sts = IntV.thread_store vss_i in
    let stk = SpecV.thread_store vsk_i in
    let d_anc = if points_to_dir sts sk_anc Left sk then Left else Right in
    
    (* we have the invariant that merkle value stored in sk_anc points to sk *)
    assert(slot_points_to_is_merkle_points_to_local sts sk_anc sk d_anc);
    
    let mv_anc = to_merkle_value (stored_value sts sk_anc) in
    // assert(mv_points_to mv_anc d_anc k);

    let k_anc = stored_key sts sk_anc in
    // assert(SpecV.store_contains stk k_anc);
    // assert(SpecV.stored_value stk k_anc = stored_value sts sk_anc);    
    SpecTS.lemma_eac_value_is_stored_value ilk_i k_anc tid;    
    lemma_mv_points_to_dir_correct ilk_i k_anc d_anc;
    lemma_ismap_correct sts sk s';
    // assert(s' = sk_anc);
    None

let proving_ancestor #vcfg
                     (ils: IntTS.hash_verifiable_log vcfg)
                     (i:I.seq_index ils)
                     (s:slot_id vcfg{let ils_i = I.prefix ils i in
                                     let vss_i = thread_state_pre ils i in
                                     let sts = IntV.thread_store vss_i in
                                     induction_props ils_i /\ 
                                     inuse_slot sts s /\ stored_key sts s <> Root}):
  pk:merkle_key{let ils_i = I.prefix ils i in
                 let vss_i = thread_state_pre ils i in
                 let sts = IntV.thread_store vss_i in
                 let k = stored_key sts s in
                 let ilk = to_logk ils in
                 let ilk_i = I.prefix ilk i in
                 pk = SpecM.proving_ancestor ilk_i k} = 
  let tid = IntTS.thread_id_of ils i in
  let ilk = to_logk ils in  
  let ils_i = I.prefix ils i in
  let ilk_i = I.prefix ilk i in
  let vss_i = thread_state_pre ils i in
  
  let sts = IntV.thread_store vss_i in

  let k = stored_key sts s in
  SpecM.proving_ancestor ilk_i k
                 
let inductive_step_addm_caseD #vcfg 
                              (ils: IntTS.hash_verifiable_log vcfg)                               
                              (i:I.seq_index ils)
                              (sk: slot_id vcfg{let ils_i = I.prefix ils i in
                                                let vss_i = IntTS.thread_state_pre ils i in
                                                let sts = IntV.thread_store vss_i in
                                                induction_props ils_i /\
                                                AddM_S? (I.index ils i) /\
                                                inuse_slot sts sk /\
                                                add_method_of sts sk = BAdd /\
                                                (let AddM_S s (k,v) s' = I.index ils i in
                                                 let k' = stored_key sts s' in                                                 
                                                 stored_key sts sk = k /\
                                                 k' = proving_ancestor ils i sk)})
  : induction_props_or_hash_collision (I.prefix ils (i + 1)) = 
  let tid = IntTS.thread_id_of ils i in
  let ilk = to_logk ils in  
  let ils_i = I.prefix ils i in
  let ilk_i = I.prefix ilk i in
  let ils_i1 = I.prefix ils (i + 1) in
  let ilk_i1 = I.prefix ilk (i + 1) in  
  let vss_i = thread_state_pre ils i in
  let vsk_i = SpecTS.thread_state_pre ilk i in
  let vsk_i1 = SpecTS.thread_state_post ilk i in
  let es = I.index ils i in
  SpecTS.lemma_verifier_thread_state_extend ilk i;

  let ek = I.index ilk i in

  match es with
  | AddM_S s (k,v) s' ->
    let sts = IntV.thread_store vss_i in
    let stk = SpecV.thread_store vsk_i in     

    lemma_addm_props vss_i es;
    let k' = stored_key sts s' in
    let v' = to_merkle_value (stored_value sts s') in
    let d = desc_dir k k' in

    // assert (SpecV.store_contains stk k);
    // assert (SpecV.add_method_of stk k = BAdd);
    SpecTS.lemma_instore_implies_eac_state_instore ilk_i k tid;
    SpecTS.lemma_eac_stored_addm ilk_i k;
    // assert (E.add_method_of (SpecTS.eac_state_of_key ilk_i k) = SpecTS.stored_add_method ilk_i k);

    let aux():
      Lemma (SpecTS.stored_tid ilk_i k = tid) = 
      let tid' = SpecTS.stored_tid ilk_i k in
      if tid' = tid then ()
      else
        SpecTS.lemma_key_in_unique_store2 ilk_i k tid tid'
    in
    aux();
    // assert (E.add_method_of (SpecTS.eac_state_of_key ilk_i k) = BAdd);
    SpecM.lemma_proving_ancestor_blum_bit ilk_i k;

    assert(SpecV.store_contains stk k');
    SpecTS.lemma_eac_value_is_stored_value ilk_i k' tid;
    assert(mv_evicted_to_blum v' d);
    None

let inductive_step_addm_caseE #vcfg 
                              (ils: IntTS.hash_verifiable_log vcfg)                               
                              (i:I.seq_index ils)
                              (sk: slot_id vcfg{let ils_i = I.prefix ils i in
                                                let vss_i = IntTS.thread_state_pre ils i in
                                                let sts = IntV.thread_store vss_i in
                                                induction_props ils_i /\
                                                AddM_S? (I.index ils i) /\
                                                inuse_slot sts sk /\
                                                (let AddM_S s (k,v) s' = I.index ils i in
                                                 let k' = stored_key sts s' in                                                 
                                                 stored_key sts sk = k /\
                                                 k' <> proving_ancestor ils i sk)})
  : induction_props_or_hash_collision (I.prefix ils (i + 1)) = 
  let tid = IntTS.thread_id_of ils i in
  let ilk = to_logk ils in  
  let ils_i = I.prefix ils i in
  let ilk_i = I.prefix ilk i in
  let ils_i1 = I.prefix ils (i + 1) in
  let ilk_i1 = I.prefix ilk (i + 1) in  
  let vss_i = thread_state_pre ils i in
  let vsk_i = SpecTS.thread_state_pre ilk i in
  let vsk_i1 = SpecTS.thread_state_post ilk i in
  let es = I.index ils i in
  SpecTS.lemma_verifier_thread_state_extend ilk i;

  let ek = I.index ilk i in

  match es with
  | AddM_S s (k,v) s' ->
    let sts = IntV.thread_store vss_i in
    let stk = SpecV.thread_store vsk_i in     

    lemma_addm_props vss_i es;
    let k' = stored_key sts s' in
    let v' = to_merkle_value (stored_value sts s') in
    let d = desc_dir k k' in

    let pk = proving_ancestor ils i sk in
    let aux () 
      : Lemma (k' = Root \/ not (SpecTS.is_eac_state_init ilk_i k')) = 
      if k' = Root then ()
      else (
        assert(SpecV.store_contains stk k');
        SpecTS.lemma_instore_implies_eac_state_instore ilk_i k' tid
      )
    in
    aux();
    lemma_init_ancestor_ancestor_of_proving ilk_i k k';
    SpecTS.lemma_eac_value_is_stored_value ilk_i k' tid;

    let k2 = mv_pointed_key v' d in

    lemma_proper_desc_depth_monotonic k pk;
    assert(is_desc k2 k);
    lemma_desc_depth_monotonic k2 k;
    assert(is_desc pk k2);
    lemma_desc_depth_monotonic pk k2;    
    None    

let inductive_step_addm #vcfg 
                       (ils: IntTS.hash_verifiable_log vcfg) 
                       (i:I.seq_index ils{let ils_i = I.prefix ils i in
                                          induction_props ils_i /\
                                          AddM_S? (I.index ils i)}): induction_props_or_hash_collision (I.prefix ils (i + 1)) = 
  let tid = IntTS.thread_id_of ils i in                                          
  let ilk = to_logk ils in  
  let ils_i = I.prefix ils i in
  let ilk_i = I.prefix ilk i in
  let ils_i1 = I.prefix ils (i + 1) in
  let ilk_i1 = I.prefix ilk (i + 1) in  
  let vss_i = thread_state_pre ils i in
  let vsk_i = SpecTS.thread_state_pre ilk i in
  let vsk_i1 = SpecTS.thread_state_post ilk i in
  let es = I.index ils i in
  SpecTS.lemma_verifier_thread_state_extend ilk i;
  
  let ek = I.index ilk i in

  match es with
  | AddM_S s (k,v) s' ->
    let sts = IntV.thread_store vss_i in
    let stk = SpecV.thread_store vsk_i in
    let k' = stored_key sts s' in
    
    if store_contains_key sts k then
      let sk = slot_of_key sts k in
      let pk = proving_ancestor ils i sk in
      if pk <> k' then
        inductive_step_addm_caseE ils i sk
      else if add_method_of sts sk = MAdd then (
        let sk_anc = IntS.pointing_slot sts sk in
        assert(inuse_slot sts sk_anc);

        let d_anc = if points_to_dir sts sk_anc Left sk then Left else Right in
        assert(slot_points_to_is_merkle_points_to_local sts sk_anc sk d_anc);
        // let mv_anc = to_merkle_value (stored_value sts sk_anc) in        
        let k_anc = stored_key sts sk_anc in

        SpecTS.lemma_eac_value_is_stored_value ilk_i k_anc tid;
        // assert(mv_anc = eac_merkle_value ilk_i k_anc);
        lemma_points_to_implies_proving_ancestor ilk_i k k_anc d_anc;
        // assert(k_anc = SpecM.proving_ancestor ilk_i k);
        
        inductive_step_addm_caseB ils i sk sk_anc
      )
      else 
        inductive_step_addm_caseD ils i sk
    
    else 
      inductive_step_addm_caseA ils i

let inductive_step_evictm #vcfg 
                       (ils: IntTS.hash_verifiable_log vcfg) 
                       (i:I.seq_index ils{let ils_i = I.prefix ils i in
                                          induction_props ils_i /\
                                          EvictM_S? (I.index ils i)}): induction_props_or_hash_collision (I.prefix ils (i + 1)) = 
  let tid = IntTS.thread_id_of ils i in                                          
  let ilk = to_logk ils in  
  let ils_i = I.prefix ils i in
  let ilk_i = I.prefix ilk i in
  let ils_i1 = I.prefix ils (i + 1) in
  let ilk_i1 = I.prefix ilk (i + 1) in  
  let vss_i = thread_state_pre ils i in
  let vsk_i = SpecTS.thread_state_pre ilk i in
  let vsk_i1 = SpecTS.thread_state_post ilk i in
  let es = I.index ils i in
  SpecTS.lemma_verifier_thread_state_extend ilk i;
  
  let ek = I.index ilk i in

  match es with
  | EvictM_S s s' ->
    lemma_evictm_simulates_spec vss_i vsk_i es;
    lemma_forall_vtls_rel_extend ils i;    
    lemma_evictm_preserves_ismap vss_i es;
    lemma_forall_store_ismap_extend ils i;
    
    if SpecTS.is_eac ilk_i1 then
      None    
    else (
      lemma_eac_boundary_inv ilk_i1 i;
      Some (lemma_non_eac_evictm_implies_hash_collision ilk_i1)
    )

let inductive_step_addb_neac_caseA #vcfg 
                       (ils: IntTS.hash_verifiable_log vcfg) 
                       (i:I.seq_index ils{let ils_i = I.prefix ils i in
                                          let ils_i1 = I.prefix ils (i + 1) in
                                          let vss_i = IntTS.thread_state_pre ils i in
                                          let sts = IntV.thread_store vss_i in
                                          let ilk_i = to_logk ils_i in
                                          let ilk_i1 = to_logk ils_i1 in
                                          induction_props ils_i /\
                                          spec_rel ils_i1 /\
                                          AddB_S? (I.index ils i) /\
                                          not (SpecTS.is_eac ilk_i1) /\
                                          SpecTS.is_eac ilk_i /\
                                          E.EACInit? (SpecTS.eac_state_pre ilk_i1 i)
                                          }): hash_collision_gen = 
  let gl = g_logS_of ils in                                          
  let ils_i = I.prefix ils i in
  let ils_i1 = I.prefix ils (i + 1) in
  let vss_i = IntTS.thread_state_pre ils i in
  let sts = IntV.thread_store vss_i in        
  let ilk_i = to_logk ils_i in
  let ilk_i1 = to_logk ils_i1 in  
  lemma_eac_boundary_inv ilk_i1 i;
  assert(SpecTS.eac_boundary ilk_i1 = i);
  let st = SpecTS.eac_state_pre ilk_i1 i in
  let ee = SpecTS.vlog_entry_ext_at ilk_i1 i in
  let es = I.index ils i in
  let ek = I.index ilk_i1 i in
  
  match es with
  | AddB_S s (k, v) t j ->
    // assert(ek = AddB (k, v) t j);
    // assert(E.to_vlog_entry ee = ek);
    // assert(st = E.EACInit);
    // assert(ee = E.NEvict ek);
    let be = IntB.blum_add_elem ils i in

    if IntB.evict_set ils `contains` be then (
      (* the evict entry be happens before i *)
      let j = IntB.index_blum_evict ils be in
      IntB.lemma_evict_before_add ils i;
      // assert(j < i);
      // the following assert needed to trigger smtpat
      assert(I.index ils j = I.index ils_i j);      
      
      // assert(IntTS.to_logK_entry ils j = I.index ilk_i1 j);
      // assert(be = IntB.blum_evict_elem ils j);
      lemma_blum_evict_elem ils i j;    
      // assert(be = IntB.blum_evict_elem ils_i j);
      lemma_spec_rel_implies_same_evict_elem ils_i j;
      // assert(be = SpecB.blum_evict_elem ilk_i j);
      // assert(SpecV.key_of (I.index ilk_i j) = k);

      SpecTS.lemma_eac_state_init_no_entry ilk_i k;
      lemma_last_index_correct2 (SpecTS.is_entry_of_key k) (I.i_seq ilk_i) j;
      hash_collision_contra()
    )
    else (      
      // assert(IntB.add_set ils `contains` be);
      // assert(IntB.add_set ils == IntG.add_set gl);
      // assert(IntB.evict_set ils == IntG.evict_set gl);
      not_eq (IntG.add_set gl) (IntG.evict_set gl) be;
      MultiHashCollision (MSCollision (IntG.add_seq gl) (IntG.evict_seq gl))
    )

let inductive_step_addb_neac_caseB #vcfg 
                       (ils: IntTS.hash_verifiable_log vcfg) 
                       (i:I.seq_index ils{let ils_i = I.prefix ils i in
                                          let ils_i1 = I.prefix ils (i + 1) in
                                          let vss_i = IntTS.thread_state_pre ils i in
                                          let sts = IntV.thread_store vss_i in
                                          let ilk_i = to_logk ils_i in
                                          let ilk_i1 = to_logk ils_i1 in
                                          induction_props ils_i /\
                                          spec_rel ils_i1 /\
                                          AddB_S? (I.index ils i) /\
                                          not (SpecTS.is_eac ilk_i1) /\
                                          SpecTS.is_eac ilk_i /\
                                          E.EACInStore? (SpecTS.eac_state_pre ilk_i1 i)
                                          }): hash_collision_gen = 
  let gl = g_logS_of ils in                                          
  // let ils_i = I.prefix ils i in
  let ils_i1 = I.prefix ils (i + 1) in
  // let vss_i = IntTS.thread_state_pre ils i in
  // let sts = IntV.thread_store vss_i in        
  // let ilk_i = to_logk ils_i in
  let ilk_i1 = to_logk ils_i1 in  
  lemma_eac_boundary_inv ilk_i1 i;
  // assert(SpecTS.eac_boundary ilk_i1 = i);
  // let st = SpecTS.eac_state_pre ilk_i1 i in
  // let ee = SpecTS.vlog_entry_ext_at ilk_i1 i in
  let es = I.index ils i in
  // let ek = I.index ilk_i1 i in

  // assert(I.length ils_i1 = (i + 1));
  // lemma_to_logk_index ils_i1 i;
  // lemma_to_logk_length ils_i1;
  // assert(I.length ilk_i1 = (i + 1));

  match es with
  | AddB_S s (k, v) t j ->
    let be = SpecB.eac_instore_addb_diff_elem ilk_i1 i in
    let _ = I.prefix ilk_i1 (i + 1) in
    // let as = SpecB.ts_add_set itsli' in
    // let es = SpecB.ts_evict_set itsli' in
    // assert(MS.mem be as > MS.mem be es);
    I.prefix_identity ilk_i1;
    // assert(ilk_i1 == itsli');
    // assert(MS.mem be (SpecB.ts_add_set ilk_i1) > MS.mem be (SpecB.ts_evict_set ilk_i1));
    // assert(IntB.add_set ils_i1 == SpecB.ts_add_set ilk_i1);
    // assert(IntB.evict_set ils_i1 == SpecB.ts_evict_set ilk_i1);
    // assert(MS.mem be (SpecB.ts_add_set ilk_i1) = MS.mem be (IntB.add_set ils_i1));
    // assert(MS.mem be (SpecB.ts_evict_set ilk_i1) = MS.mem be (IntB.evict_set ils_i1));
    
    
    lemma_add_delta_implies_not_eq ils (i + 1) be;
    // assert(~ (IntB.add_set ils == IntB.evict_set ils));
    // assert(IntB.add_set ils == IntG.add_set gl);
    // assert(IntB.evict_set ils == IntG.evict_set gl);
    // assert(~ (IntG.add_set gl == IntG.evict_set gl));
    // let s1 = (IntG.add_seq gl) in
    // let s2 = IntG.evict_seq gl in
    // assert(ms_hashfn s1 = ms_hashfn s2);

    // assert(seq2mset #_ #ms_hashfn_dom_cmp s1 == IntG.add_set gl);
    // assert(seq2mset #_ #ms_hashfn_dom_cmp s2 == IntG.evict_set gl);
    MultiHashCollision (MSCollision (IntG.add_seq gl) (IntG.evict_seq gl))


let inductive_step_addb_neac_caseC #vcfg 
                       (ils: IntTS.hash_verifiable_log vcfg) 
                       (i:I.seq_index ils{let ils_i = I.prefix ils i in
                                          let ils_i1 = I.prefix ils (i + 1) in
                                          let vss_i = IntTS.thread_state_pre ils i in
                                          let sts = IntV.thread_store vss_i in
                                          let ilk_i = to_logk ils_i in
                                          let ilk_i1 = to_logk ils_i1 in
                                          induction_props ils_i /\
                                          spec_rel ils_i1 /\
                                          AddB_S? (I.index ils i) /\
                                          not (SpecTS.is_eac ilk_i1) /\
                                          SpecTS.is_eac ilk_i /\
                                          E.EACEvictedMerkle? (SpecTS.eac_state_pre ilk_i1 i)
                                          }): hash_collision_gen = admit()

let inductive_step_addb_neac_caseD #vcfg 
                       (ils: IntTS.hash_verifiable_log vcfg) 
                       (i:I.seq_index ils{let ils_i = I.prefix ils i in
                                          let ils_i1 = I.prefix ils (i + 1) in
                                          let vss_i = IntTS.thread_state_pre ils i in
                                          let sts = IntV.thread_store vss_i in
                                          let ilk_i = to_logk ils_i in
                                          let ilk_i1 = to_logk ils_i1 in
                                          induction_props ils_i /\
                                          spec_rel ils_i1 /\
                                          AddB_S? (I.index ils i) /\
                                          not (SpecTS.is_eac ilk_i1) /\
                                          SpecTS.is_eac ilk_i /\
                                          E.EACEvictedBlum? (SpecTS.eac_state_pre ilk_i1 i)
                                          }): hash_collision_gen = admit()

let inductive_step_addb_neac #vcfg 
                       (ils: IntTS.hash_verifiable_log vcfg) 
                       (i:I.seq_index ils{let ils_i = I.prefix ils i in
                                          let ils_i1 = I.prefix ils (i + 1) in
                                          let vss_i = IntTS.thread_state_pre ils i in
                                          let sts = IntV.thread_store vss_i in
                                          let ilk_i = to_logk ils_i in
                                          let ilk_i1 = to_logk ils_i1 in
                                          induction_props ils_i /\
                                          spec_rel ils_i1 /\
                                          AddB_S? (I.index ils i) /\
                                          not (SpecTS.is_eac ilk_i1) /\
                                          SpecTS.is_eac ilk_i}): hash_collision_gen =
  let ils_i = I.prefix ils i in
  let ils_i1 = I.prefix ils (i + 1) in
  let vss_i = IntTS.thread_state_pre ils i in
  let sts = IntV.thread_store vss_i in                       
  let ilk_i1 = to_logk ils_i1 in  
  lemma_eac_boundary_inv ilk_i1 i;
  assert(SpecTS.eac_boundary ilk_i1 = i);
  let st = SpecTS.eac_state_pre ilk_i1 i in
  let ee = SpecTS.vlog_entry_ext_at ilk_i1 i in
  let es = I.index ils i in
  let ek = I.index ilk_i1 i in
  
  match es with
  | AddB_S s (k, v) t j ->
    // assert(ek = AddB (k, v) t j);
    // assert(E.to_vlog_entry ee = ek);

    match st with
    | E.EACInit -> (
      match ee with
      | E.NEvict (AddB _ _ _) -> inductive_step_addb_neac_caseA ils i
      )
    | E.EACInStore _ _ -> (
      match ee with
      | E.NEvict (AddB _ _ _) -> inductive_step_addb_neac_caseB ils i
      )
    | E.EACEvictedMerkle _ -> (
      match ee with
      | E.NEvict (AddB _ _ _) -> inductive_step_addb_neac_caseC ils i
      )
    | E.EACEvictedBlum _ _ _ -> (
      match ee with
      | E.NEvict (AddB _ _ _) -> inductive_step_addb_neac_caseD ils i
      )

let inductive_step_addb_caseA #vcfg 
                       (ils: IntTS.hash_verifiable_log vcfg) 
                       (i:I.seq_index ils{let ils_i = I.prefix ils i in
                                          let vss_i = IntTS.thread_state_pre ils i in
                                          let sts = IntV.thread_store vss_i in                       
                                          induction_props ils_i /\
                                          AddB_S? (I.index ils i) /\
                                          (let AddB_S _ (k,_) _ _ = I.index ils i in
                                           not (store_contains_key sts k)                                          
                                          )}): induction_props_or_hash_collision (I.prefix ils (i + 1)) = 
  let tid = IntTS.thread_id_of ils i in                                          
  let ilk = to_logk ils in  
  let ils_i = I.prefix ils i in
  let ilk_i = I.prefix ilk i in
  let ils_i1 = I.prefix ils (i + 1) in
  let ilk_i1 = I.prefix ilk (i + 1) in  
  let vss_i = thread_state_pre ils i in
  let vsk_i = SpecTS.thread_state_pre ilk i in
  let vsk_i1 = SpecTS.thread_state_post ilk i in
  let es = I.index ils i in
  SpecTS.lemma_verifier_thread_state_extend ilk i;
  
  let ek = I.index ilk i in

  match es with
  | AddB_S s (k,v) t j ->
    lemma_vaddb_preserves_spec_new_key vss_i vsk_i es;
    lemma_forall_vtls_rel_extend ils i;    
    lemma_vaddb_preserves_ismap_new_key vss_i es;
    lemma_forall_store_ismap_extend ils i;

    if SpecTS.is_eac ilk_i1 then None
    else (
      lemma_eac_boundary_inv ilk_i1 i;
      assert(SpecTS.eac_boundary ilk_i1 = i);
      
      admit()
    )

(* 
 * induction step: if all the induction properties hold for prefix of length i, 
 * then the properties hold for prefix of length (i + 1) or we construct 
 * a hash collision
 *)
let inductive_step #vcfg 
                   (ils: IntTS.hash_verifiable_log vcfg) 
                   (i:I.seq_index ils{let ils_i = I.prefix ils i in
                                      induction_props ils_i}): induction_props_or_hash_collision (I.prefix ils (i + 1)) = 
  let es = I.index ils i in 
  match es with
  | Get_S _ _ _ -> inductive_step_get ils i
  | Put_S _ _ _ -> inductive_step_put ils i  
  | AddM_S _ _ _ -> inductive_step_addm ils i
  | EvictM_S _ _ -> inductive_step_evictm ils i
  | _ -> admit()                                      

let lemma_empty_implies_induction_props #vcfg (ils: its_log vcfg{I.length ils = 0})
  : Lemma (ensures (induction_props ils)) 
  = admit()          

let rec lemma_hash_verifiable_implies_induction_props_or_hash_collision_aux 
        #vcfg 
        (ils: hash_verifiable_log vcfg)
        (i:nat{i <= I.length ils})
  : Tot (induction_props_or_hash_collision (I.prefix ils i))
    (decreases i) = 
  let ils_i = I.prefix ils i in
  if i = 0 then (
     lemma_empty_implies_induction_props ils_i;
     None
  )
  else 
    let hc_or_props = lemma_hash_verifiable_implies_induction_props_or_hash_collision_aux ils (i - 1) in
    
    (* we found a hash collision - simply return the same *)
    if Some? hc_or_props then
      Some (Some?.v hc_or_props)
    else
      inductive_step ils (i - 1)
  
let lemma_hash_verifiable_implies_induction_props_or_hash_collision #vcfg (ils: hash_verifiable_log vcfg)
  : induction_props_or_hash_collision ils = 
  I.lemma_fullprefix_equal ils;
  lemma_hash_verifiable_implies_induction_props_or_hash_collision_aux ils (I.length ils)
  
let lemma_time_seq_rw_consistent #vcfg
                                 (ils: IntTS.hash_verifiable_log vcfg {~ (rw_consistent (IntTS.to_state_ops ils))})
  : hash_collision_gen = 
  let ts_ops = IntTS.to_state_ops ils in
  let hc_or_props = lemma_hash_verifiable_implies_induction_props_or_hash_collision ils in
  
  (* if hc_or_inv returns a hash collision, then we can return the same collision *)
  if Some? hc_or_props
    then Some?.v hc_or_props

  (* otherwise, we can use the spec-level lemma *)
  else 
    let ilk = IntTS.to_logk ils in
    SpecC.lemma_time_seq_rw_consistent ilk
  
// final correctness property
let lemma_verifier_correct (#vcfg:_) (gl: IntG.hash_verifiable_log vcfg { ~ (seq_consistent (IntG.to_state_ops gl))})
  : hash_collision_gen = 
  (* sequences of per-thread put/get operations *)
  let g_ops = IntG.to_state_ops gl in
  
  (* sequence ordered by time of each log entry *)
  let il = IntTS.create gl in  
  I.lemma_interleaving_correct il;
  assert(I.interleave (I.i_seq il) gl);

  (* sequence of state ops induced by tmsl *)
  let ts_ops = IntTS.to_state_ops il in
  IntTS.lemma_logS_interleave_implies_state_ops_interleave (I.i_seq il) gl;
  assert(I.interleave ts_ops g_ops);

  let is_rw_consistent = valid_all_comp ssm ts_ops in
  lemma_state_sm_equiv_rw_consistent ts_ops;

    if is_rw_consistent then (
      assert(valid_all ssm ts_ops);
      assert(rw_consistent ts_ops);

      (* a contradiction *)
      assert(seq_consistent g_ops);

      (* any return value *)
      SingleHashCollision (Collision (DVal Null) (DVal Null))
    )
    else
      lemma_time_seq_rw_consistent il
