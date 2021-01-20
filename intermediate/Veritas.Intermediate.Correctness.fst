module Veritas.Intermediate.Correctness

open Veritas.Hash
open Veritas.Record
open Veritas.SeqMachine
open Veritas.State
open Veritas.StateSeqMachine
open Veritas.Verifier
open Veritas.Verifier.EAC
open Veritas.Intermediate.Global
open Veritas.Intermediate.Logs
open Veritas.Intermediate.Thread
open Veritas.Intermediate.TSLog
open Veritas.Intermediate.Verify
open Veritas.Intermediate.VerifierConfig

module I = Veritas.Interleave
module IntL = Veritas.Intermediate.Logs
module IntG = Veritas.Intermediate.Global
module IntV = Veritas.Intermediate.Verify
module IntS = Veritas.Intermediate.Store
module IntTS = Veritas.Intermediate.TSLog
module SpecTS = Veritas.Verifier.TSLog
module SpecC = Veritas.Verifier.Correctness

(* 
 * A bunch of properties we use in the induction step:
 *    (a) the intermediate verifiers all satisfy the store invariant
 *    (b) the intermediate and spec level verifiers states correspond to one-another (related)
 *    (c) the spec level log is time sorted (b and c imply that the spec log has type its_log)
 *    (d) the spec level log is evict-add-consistent 
 *)
let induction_props #vcfg (ils: its_log vcfg) = 
  let ilk = IntTS.to_logk ils in
  IntTS.forall_store_ismap ils /\
  IntTS.forall_vtls_rel ils /\
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
  | IntL.Get_S _ _ _ -> inductive_step_get ils i
  | IntL.Put_S _ _ _ -> inductive_step_put ils i  
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
