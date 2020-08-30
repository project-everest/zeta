module Veritas.Verifier.EAC

open Veritas.BinTree
open Veritas.EAC
open Veritas.Hash
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSet
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.SeqMachine
open Veritas.State
open Veritas.Verifier
open Veritas.Verifier.Blum
open Veritas.Verifier.Global
open Veritas.Verifier.Merkle
open Veritas.Verifier.Thread
open Veritas.Verifier.TSLog

open FStar.Seq
open Veritas.SeqAux

module I = Veritas.Interleave
module EC = Veritas.EAC
module MS = Veritas.MultiSet
module MH = Veritas.MultiSetHash
module TL = Veritas.Verifier.TSLog
module V = Veritas.Verifier
module VG = Veritas.Verifier.Global
module VT = Veritas.Verifier.Thread

(* generalized single- and multi-set hash collision *)
type hash_collision_gen =
  | SingleHashCollision: hc: hash_collision -> hash_collision_gen
  | MultiHashCollision: hc: ms_hash_collision -> hash_collision_gen

(* construct a hash collision from a contradiction *)
let hash_collision_contra (_:unit{False}): hash_collision_gen =
  SingleHashCollision (Collision (DVal Null) (DVal Null))

(* if an operation requires the key in store, it cannot be the first operation *)
let lemma_non_eac_init_requires_key_in_store
  (itsl: neac_log {
    eac_boundary_state_pre itsl = EACInit /\
    requires_key_in_store (eac_boundary_entry itsl) /\
    Root <> key_of (eac_boundary_entry itsl)
  }):
  hash_collision_gen =
  // maximum prefix of itsl that is eac
  let i = eac_boundary itsl in
  let itsli = I.prefix itsl i in

  // vlog entry e going at thread tid causes the eac failure
  let e = I.index itsl i in
  let k = V.key_of e in
  let tid = thread_id_of itsl i in

  // Store of tid does not contain the key k after processing i elements
  TL.lemma_eac_state_init_store itsli k tid;
  //assert(not (store_contains (thread_store itsli tid) k));

  // but we know that the tid state is still valid after processing e
  // which does require k to be in the store, a contradiction
  hash_collision_contra ()

(* the first operation for a key cannot be evict *)
let lemma_non_eac_init_evict
  (itsl: neac_log {
    eac_boundary_state_pre itsl = EACInit /\
    V.is_evict (eac_boundary_entry itsl)
  }): hash_collision_gen =
  let i = TL.eac_boundary itsl in
  TL.lemma_root_never_evicted itsl i;
  lemma_non_eac_init_requires_key_in_store itsl

(* the first operation for a key cannot be a blum add *)
let lemma_non_eac_init_addb
  (itsl: neac_log {
    TL.hash_verifiable itsl /\
    eac_boundary_state_pre itsl = EACInit /\
    is_blum_add (eac_boundary_entry itsl)}): hash_collision_gen =

  (* the maximum eac prefix of itsl *)
  let i = eac_boundary itsl in
  let itsli = I.prefix itsl i in

  let gl = g_vlog_of itsl in

  // the blum add element corresponding to the boundary
  let e = I.index itsl i in
  let k = key_of e in
  let be = blum_add_elem (I.index itsl i) in

  // since k is in init_state after processing i entries, there cannot
  // be a prior entry for k
  lemma_eac_state_init_no_entry itsli k;
  //assert(not (has_some_entry_of_key itsli k));

  if MS.contains be (ts_evict_set itsl) then (
    (* the evict that corresponds to blum add happens before i *)
    let j = index_blum_evict itsl be in
    lemma_evict_before_add itsl i;
    //assert(j < i);

    (* this emplies itsli contains an entry with key k *)
    (* a contradiction *)
    assert(index (I.i_seq itsli) j = I.index itsli j);
    lemma_last_index_correct2 (is_entry_of_key k) (I.i_seq itsli) j;
    hash_collision_contra ()
  )
  else (
    (* since be is in add set, but not in evict set they cannot be the same *)
    lemma_add_elem_correct itsl i;
    lemma_ts_add_set_correct itsl;
    lemma_ts_evict_set_correct itsl;
    MS.lemma_not_equal (g_add_set gl) (g_evict_set gl) be;
    //assert(~ (g_add_set gl == g_evict_set gl));

    lemma_g_hadd_correct gl;
    lemma_ghevict_correct gl;

    MultiHashCollision (MSCollision (g_add_seq gl) (g_evict_seq gl))
  )

let lemma_non_eac_init_addm
  (itsl: neac_log{
    eac_boundary_state_pre itsl = EACInit /\
    is_merkle_add (eac_boundary_entry itsl)
   })
  : hash_collision_gen =
  (* the maximum eac prefix of itsl *)
  let i = eac_boundary itsl in
  let itsli = I.prefix itsl i in
  let itsli' = I.prefix itsl (i + 1) in

  // vlog entry e going at thread tid causes the eac failure
  let e = I.index itsl i in
  let k = V.key_of e in
  let tid = thread_id_of itsl i in
  let ee = TL.vlog_entry_ext_at itsl i in

  //assert(eac_add ee (eac_boundary_state_pre itsl) = EACFail);                 
  match e with
  | AddM (k,v) k' ->
    
    (* otherwise eac_add ee (boundary_state ...) <> EACFail *)
    // assert(v <> init_value k);

    (* verifier checks this *)
    // assert(is_proper_desc k k');

    (* k' is the proving ancestor of k*)
    lemma_addm_ancestor_is_proving itsli';
    //assert(k' = proving_ancestor itsli k);

    (* k' is the verifier cache *)
    //assert(store_contains (thread_store itsli tid) k');

    lemma_eac_value_is_stored_value itsli k' tid;
    //assert(eac_value itsli k' = V.stored_value (thread_store itsli tid) k');

    let v' = eac_merkle_value itsli k' in
    //assert(v' = to_merkle_value(V.stored_value (thread_store itsli tid) k'));

    let d = desc_dir k k' in
    let dh' = desc_hash_dir v' d in

    (* k' points to none or some non-ancestor of k *)
    //assert(is_eac_state_init itsli k);
    lemma_proving_ancestor_initial itsli k;
    //assert(mv_points_to_none v' d \/ not (is_desc k (mv_pointed_key v' d)));

    match dh' with
    | Empty -> hash_collision_contra()
    | Desc k2 _ _ ->
      //assert(not (is_desc k k2));
      lemma_desc_reflexive k;
      //assert(k <> k2);
      hash_collision_contra()


let lemma_non_eac_instore_get
  (itsl: neac_log {
    EACInStore? (eac_boundary_state_pre itsl) /\
    Get? (eac_boundary_entry itsl)
   })
  : hash_collision_gen =
  let st = eac_boundary_state_pre itsl in

  (* the maximum eac prefix of itsl *)
  let i = eac_boundary itsl in
  let itsli = I.prefix itsl i in

  // vlog entry e going at thread tid causes the eac failure
  let e = I.index itsl i in
  let k = V.key_of e in
  let tid = thread_id_of itsl i in
  let ee = TL.vlog_entry_ext_at itsl i in

  match st with
  | EACInStore m v -> (
    match ee with
    | NEvict (Get k v') ->
      (* otherwise there will not be an eac failure *)
      assert(DVal v' <> v);

      (* instore state implies that k is in some (unique) thread store *)
      let tid_stored = stored_tid itsli k in

      if tid_stored = tid then (

        (* the verifier checks that the stored value is the value v' in Get *)
        //assert(DVal v' = stored_value itsli k);

        (* for data keys, the value in EACInStore state v is equal to the stored value *)
        lemma_eac_stored_value itsli k;
        //assert(stored_value itsli k = v);

        (* this implies a contradiction *)
        hash_collision_contra()        
      )
      else (
        (* since tid <> tid_stored, k is not in store of tid *)
        lemma_key_in_unique_store itsli k tid;

        (* this gives a contradiction since for verification k has to be in store of tid *)
        hash_collision_contra()
      )
  )

let lemma_non_eac_instore_put
  (itsl: neac_log {
    EACInStore? (eac_boundary_state_pre itsl) /\
    Put? (eac_boundary_entry itsl)
   })
  : hash_collision_gen =
  let st = eac_boundary_state_pre itsl in

  (* the maximum eac prefix of itsl *)
  let i = eac_boundary itsl in
  let itsli = I.prefix itsl i in

  // vlog entry e going at thread tid causes the eac failure
  let e = I.index itsl i in
  let k = V.key_of e in
  let tid = thread_id_of itsl i in
  let ee = TL.vlog_entry_ext_at itsl i in

  match st with
  | EACInStore m v -> (
    match ee with
    | NEvict (Put k v') ->
      (* otherwise there will not be an eac failure *)
      assert(not (DVal? v));

      (* for any EACInStore v, the value of v is the type of k *)
      (* this implies DVal? v since k is a data key *)
      lemma_eac_value_correct_type itsli k;

      (* this gives a contradiction since for verification k has to be in store of tid *)
      hash_collision_contra()
  )

let lemma_non_eac_instore_addb
  (itsl: neac_log {
    TL.hash_verifiable itsl /\
    EACInStore? (eac_boundary_state_pre itsl) /\
    AddB? (eac_boundary_entry itsl)
   })
  : hash_collision_gen =
  let gl = g_vlog_of itsl in  
  
  (* the maximum eac prefix of itsl *)
  let i = eac_boundary itsl in
  let itsli = I.prefix itsl i in
  let itsli' = I.prefix itsl (i + 1) in

  // vlog entry e going at thread tid causes the eac failure
  let e = I.index itsl i in
  let k = V.key_of e in
  let tid = thread_id_of itsl i in
  let ee = TL.vlog_entry_ext_at itsl i in

  (* number of blum evicts is the same as blum adds in the first i entries *)
  lemma_evict_add_count_same itsli k;
  //assert(MS.size (ts_add_set_key itsli k) = MS.size (ts_evict_set_key itsli k));

  (* the ith element is a blum add *)
  //assert(is_blum_add e);  
  assert(I.index itsl i = I.index itsli' i);
  lemma_ts_add_set_key_extend itsli';  
  //assert(ts_add_set_key itsli' k == add_elem (ts_add_set_key itsli k) (blum_add_elem e));

  (* the ith element is not a blum evict *)
  //assert(not (is_evict_to_blum (I.index itsl i)));
  lemma_ts_evict_set_key_extend2 itsli';
  //assert(ts_evict_set_key itsli' k == ts_evict_set_key itsli k);

  (* this implies that the size of the add set after processing (i+1) elements
   * is one larger than the evict set at this point *)
  //assert(MS.size (ts_add_set_key itsli' k) = 1 + (MS.size (ts_evict_set_key itsli' k)));

  (* this implies that in the first (i+1) entries there is an element whose membership in
   * add multiset is > its membership in evict multiset *)
  let be = diff_elem (ts_add_set_key itsli' k) (ts_evict_set_key itsli' k) in
  //assert(MS.contains be (ts_add_set_key itsli' k));
  lemma_ts_add_set_key_contains_only itsli' k be;
  //assert(MH.key_of be = k);
  lemma_mem_key_add_set_same itsli' be;
  lemma_mem_key_evict_set_same itsli' be;
  //assert(MS.mem be (ts_add_set itsli') > MS.mem be (ts_evict_set itsli'));

  (* the index of be in the add set *)
  let i_be = some_add_elem_idx itsli' be in
  //assert(i_be <= i);

  (* from clock orderedness any evict_set entry for be should happen before i *)
  lemma_evict_before_add2 itsl i_be;
  //assert(MS.mem be (ts_evict_set itsl) = MS.mem be (ts_evict_set (I.prefix itsl i_be)));

  (* any set membership is monotonic *)
  lemma_mem_monotonic be itsl (i + 1);
  lemma_mem_monotonic be itsli' i_be;
  //assert(MS.mem be (ts_add_set itsl) >= MS.mem be (ts_add_set itsli'));
  //assert(MS.mem be (ts_evict_set itsl) = MS.mem be (ts_evict_set itsli'));

  (* this implies the membership of be in (overall) addset > membership in evict set *)
  (* so these two sets are not equal providing a hash collision *)
  //assert(MS.mem be (ts_add_set itsl) > MS.mem be (ts_evict_set itsl));

  MS.lemma_not_equal (ts_add_set itsl) (ts_evict_set itsl) be;
  //assert(~( (ts_add_set itsl) == (ts_evict_set itsl)));

  lemma_ts_add_set_correct itsl;
  lemma_ts_evict_set_correct itsl;
  //assert(~ (g_add_set gl == g_evict_set gl));


  lemma_g_hadd_correct gl;
  lemma_ghevict_correct gl;

  MultiHashCollision (MSCollision (g_add_seq gl) (g_evict_seq gl))


let lemma_non_eac_instore_addm
  (itsl: neac_log {
    EACInStore? (eac_boundary_state_pre itsl) /\
    AddM? (eac_boundary_entry itsl)
   })
  : hash_collision_gen =
  (* the maximum eac prefix of itsl *)
  let i = eac_boundary itsl in
  let itsli = I.prefix itsl i in
  let itsli' = I.prefix itsl (i + 1) in

  // vlog entry e going at thread tid causes the eac failure
  let e = I.index itsl i in
  let k = V.key_of e in
  let tid = thread_id_of itsl i in
  let ee = TL.vlog_entry_ext_at itsl i in

  (* instore state implies that k is in some (unique) thread store *)
  let tid_stored = stored_tid itsli k in

  (* if store already contains k, adding should cause verification failure *)
  if tid = tid_stored then
    hash_collision_contra()  
      
  else (
    match e with
    | AddM _ k' ->

    (* k' is the proving ancestor of k *)
    lemma_addm_ancestor_is_proving itsli';
    //assert(k' = proving_ancestor itsli k);

    (* thread store of tid contains k' *)
    //assert(store_contains (TL.thread_store itsli tid) k');

    (* k is present in the store of tid_stored, by definition *)
    //assert(store_contains (TL.thread_store itsli tid_stored) k);

    (* this implies k' is in the store of ltid *)
    lemma_store_contains_proving_ancestor itsli tid_stored k;    
    //assert(store_contains (TL.thread_store itsli tid_stored) k');

    (* but k' cannot be in two stores *)
    lemma_key_in_unique_store2 itsli k' tid tid_stored;

    hash_collision_contra()
  )

let lemma_non_eac_instore_evictm
  (itsl: neac_log {
    EACInStore? (eac_boundary_state_pre itsl) /\
    EvictM? (eac_boundary_entry itsl)
   })
  : hash_collision_gen =

  let st = eac_boundary_state_pre itsl in

  (* the maximum eac prefix of itsl *)
  let i = eac_boundary itsl in
  let itsli = I.prefix itsl i in

  // vlog entry e going at thread tid causes the eac failure
  let e = I.index itsl i in
  let k = V.key_of e in
  let tid = thread_id_of itsl i in
  let ee = TL.vlog_entry_ext_at itsl i in

  match st with
  | EACInStore m v -> (
    match ee with
    | EvictMerkle (EvictM k k') v' ->
      (* otherwise we would not have an eac failure *)
      //assert(DVal? v && v' <> v);

      (* since DVal? v, k should be a data key *)
      lemma_eac_value_correct_type itsli k;
      //assert(is_data_key k);

      (* ee is constructed by using the stored value, so ... *)
      lemma_ext_evict_val_is_stored_val itsl i;
      //assert(v' = V.stored_value (thread_store itsli tid) k);

      lemma_key_in_unique_store itsli k tid;
      //assert(tid = stored_tid itsli k);
      //assert(V.stored_value (thread_store itsli tid) k = TL.stored_value itsli k);

      (* for data keys, the value in EACInStore is identical to the stored value *)
      lemma_eac_stored_value itsli k;
      
      (* ... which provides a contradiction *)
      hash_collision_contra()
    )

let lemma_non_eac_instore_evictb
  (itsl: neac_log {
    EACInStore? (eac_boundary_state_pre itsl) /\
    EvictB? (eac_boundary_entry itsl)
   })
  : hash_collision_gen =
  let st = eac_boundary_state_pre itsl in

  (* the maximum eac prefix of itsl *)
  let i = eac_boundary itsl in
  let itsli = I.prefix itsl i in

  // vlog entry e going at thread tid causes the eac failure
  let e = I.index itsl i in
  let k = V.key_of e in
  let tid = thread_id_of itsl i in
  let ee = TL.vlog_entry_ext_at itsl i in

  match st with
  | EACInStore m v -> (
    match ee with
    | EvictBlum (EvictB k t) v' tid' ->
      (* otherwise there won't be an eac failure *)
      // assert(DVal? v && v' <> v || m <> BAdd);

      (* the thread store of tid contains k *)
      // assert(store_contains (thread_store itsli tid) k);

      (* key k is in only one store *)
      lemma_key_in_unique_store itsli k tid;
      // assert(stored_tid itsli k = tid);

      (* the add method stored with k is m *)
      lemma_eac_stored_addm itsli k;
      // assert(m = stored_add_method itsli k);

      (* since the verifier checks that the stored add method is blum, we have *)
      // assert(m = BAdd);

      (* this implies *)
      // assert(DVal? v && v' <> v);

      (* the eac value is always the correct type based on key k *)
      lemma_eac_value_correct_type itsli k;
      // assert(is_data_key k);

      lemma_eac_stored_value itsli k;
      // assert(v = stored_value itsli k);

      lemma_ext_evict_val_is_stored_val itsl i;
      // assert(v' = stored_value itsli k);

      hash_collision_contra()
  )


let lemma_non_eac_instore_evictbm
  (itsl: neac_log {
    EACInStore? (eac_boundary_state_pre itsl) /\
    EvictBM? (eac_boundary_entry itsl)
   })
  : hash_collision_gen =

  let st = eac_boundary_state_pre itsl in

  (* the maximum eac prefix of itsl *)
  let i = eac_boundary itsl in
  let itsli = I.prefix itsl i in

  // vlog entry e going at thread tid causes the eac failure
  let e = I.index itsl i in
  let k = V.key_of e in
  let tid = thread_id_of itsl i in
  let ee = TL.vlog_entry_ext_at itsl i in

  match st with
  | EACInStore m v -> (
    match ee with
    | EvictBlum (EvictBM k k' t) v' tid' ->
      (* otherwise there won't be an eac failure *)
      // assert(DVal? v && v' <> v || m <> MAdd);

      (* the thread store of tid contains k *)
      // assert(store_contains (thread_store itsli tid) k);

      (* key k is in only one store *)
      lemma_key_in_unique_store itsli k tid;
      // assert(stored_tid itsli k = tid);

      (* the add method stored with k is m *)
      lemma_eac_stored_addm itsli k;
      // assert(m = stored_add_method itsli k);

      (* since the verifier checks that the stored add method is merkle, we have *)
      // assert(m = MAdd);

      (* this implies *)
      // assert(DVal? v && v' <> v);

      (* the eac value is always the correct type based on key k *)
      lemma_eac_value_correct_type itsli k;
      // assert(is_data_key k);


      lemma_eac_stored_value itsli k;
      // assert(v = stored_value itsli k);


      lemma_ext_evict_val_is_stored_val itsl i;
      // assert(v' = stored_value itsli k);

      hash_collision_contra()
  )  

let lemma_non_eac_evicted_requires_key_in_store
  (itsl: neac_log {
    EC.is_eac_state_evicted (eac_boundary_state_pre itsl) /\
    requires_key_in_store (eac_boundary_entry itsl)
   })
  : hash_collision_gen =

  let st = eac_boundary_state_pre itsl in

  (* the maximum eac prefix of itsl *)
  let i = eac_boundary itsl in
  let itsli = I.prefix itsl i in

  // vlog entry e going at thread tid causes the eac failure
  let e = I.index itsl i in
  let k = V.key_of e in
  let tid = thread_id_of itsl i in
  let ee = TL.vlog_entry_ext_at itsl i in

  (* since e requires the store to contain the key k for verification success *)
  assert(V.store_contains (thread_store itsli tid) k);

  (* evicted => no store contains k, a contradiction *)
  lemma_eac_state_evicted_store itsli k tid;

  hash_collision_contra()


(*

let lemma_non_eac_evicted_requires_key_in_store (#p:pos)
  (itsl: non_eac_ts_log p{
    EC.is_eac_state_evicted (last_valid_eac_state itsl)  /\
    requires_key_in_store (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen =
  let st = last_valid_eac_state itsl in
  let ee = invalidating_log_entry itsl in
  assert(eac_add ee st = EACFail);

  let tsle = time_seq_ext itsl in
  let i = max_eac_prefix tsle in
  let (e,tid) = index itsl i in
  let k = V.key_of e in
  let itsli = prefix itsl i in
  (* verifier thread state of tid after itsli *)
  let vsi = verifier_thread_state itsli tid in

  let itsli' = prefix itsl (i + 1) in
  let vsi' = verifier_thread_state itsli' tid in
  lemma_verifier_thread_state_extend itsli';
  assert(vsi' == t_verify_step vsi e);

  assert(store_contains (thread_store vsi) k);
  lemma_eac_state_evicted_store itsli k tid;
  hash_collision_contra()

let lemma_non_eac_evicted_merkle_addm (#p:pos)
  (itsl: non_eac_ts_log p{
    EACEvictedMerkle? (last_valid_eac_state itsl)  /\
    AddM? (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen =
  let st = last_valid_eac_state itsl in
  let ee = invalidating_log_entry itsl in
  assert(eac_add ee st = EACFail);
  match st with
  | EACEvictedMerkle v_e -> (
    match ee with
    | NEvict (AddM (k,v) k') ->
      assert(v_e <> v);
      let tsle = time_seq_ext itsl in
      let i = max_eac_prefix tsle in
      let (e,tid) = index itsl i in

      let itsli = prefix itsl i in
      (* verifier thread state of tid after itsli *)
      let vsi = verifier_thread_state itsli tid in

      let itsli' = prefix itsl (i + 1) in
      let vsi' = verifier_thread_state itsli' tid in
      lemma_verifier_thread_state_extend itsli';
      assert(vsi' == t_verify_step vsi e);

      (* k' is a proper ancestor, so k cannot be root *)
      assert(k <> Root);

      (* k' is the proving ancestor of k *)
      lemma_addm_ancestor_is_proving itsli';
      assert(k' = proving_ancestor itsli k);

      (* k' points to k *)
      lemma_proving_ancestor_points_to_self itsli k;
      lemma_eac_value_is_stored_value itsli k' tid;
      let mv' = to_merkle_value (stored_value (thread_store vsi) k') in
      let d = desc_dir k k' in
      let dh = desc_hash_dir mv' d in
      assert(Desc?.k dh = k);

      (* verifier checks for addm *)
      assert(Desc?.h dh = hashfn v);

      assert(is_eac_state_evicted_merkle itsli k);
      lemma_proving_ancestor_has_hash itsli k;
      lemma_eac_value_is_evicted_value itsli k;
      assert(Desc?.h dh = hashfn v_e);

      (* which gives us a hash collision *)
      SingleHashCollision (Collision v v_e)
    )

let lemma_non_eac_evicted_blum_addm (#p:pos)
  (itsl: non_eac_ts_log p{
    EACEvictedBlum? (last_valid_eac_state itsl)  /\
    AddM? (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen =
  let st = last_valid_eac_state itsl in
  let ee = invalidating_log_entry itsl in
  assert(eac_add ee st = EACFail);
  match st with
  | EACEvictedBlum v_e _ _ -> (
    match ee with
    | NEvict (AddM (k,v) k') ->
      let tsle = time_seq_ext itsl in
      let i = max_eac_prefix tsle in
      let (e,tid) = index itsl i in

      let itsli = prefix itsl i in
      (* verifier thread state of tid after itsli *)
      let vsi = verifier_thread_state itsli tid in

      let itsli' = prefix itsl (i + 1) in
      let vsi' = verifier_thread_state itsli' tid in
      lemma_verifier_thread_state_extend itsli';
      assert(vsi' == t_verify_step vsi e);

      (* k' is a proper ancestor, so k cannot be root *)
      assert(k <> Root);

      (* k' is the proving ancestor of k *)
      lemma_addm_ancestor_is_proving itsli';
      assert(k' = proving_ancestor itsli k);

      (* k' points to k *)
      lemma_proving_ancestor_points_to_self itsli k;
      lemma_eac_value_is_stored_value itsli k' tid;
      let mv' = to_merkle_value (stored_value (thread_store vsi) k') in
      let d = desc_dir k k' in
      let dh = desc_hash_dir mv' d in
      assert(Desc?.k dh = k);
      assert(Desc?.b dh = false);

      (* since m = BAdd, this bit should be set to true, a contradiction *)
      lemma_proving_ancestor_blum_bit itsli k;
      hash_collision_contra()
  )

let lemma_non_eac_evicted_merkle_addb (#p:pos)
  (itsl: non_eac_ts_log p{
    VG.hash_verifiable (partition_idx_seq itsl) /\
    EACEvictedMerkle? (last_valid_eac_state itsl)  /\
    AddB? (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen =
  (* hash verifiable - evict hash and add hash equal *)
  let gl = partition_idx_seq itsl in
  assert(VG.hadd gl = VG.hevict gl);

  let st = last_valid_eac_state itsl in
  let ee = invalidating_log_entry itsl in
  assert(eac_add ee st = EACFail);
  match st with
  | EACEvictedMerkle v_e -> (
    match ee with
    | NEvict (AddB (k,v) t j) ->
      let tsle = time_seq_ext itsl in
      let i = max_eac_prefix tsle in
      let (e,tid) = index itsl i in

      let itsli = prefix itsl i in
      (* verifier thread state of tid after itsli *)
      let vsi = verifier_thread_state itsli tid in

      let itsli' = prefix itsl (i + 1) in
      let vsi' = verifier_thread_state itsli' tid in
      lemma_verifier_thread_state_extend itsli';
      assert(vsi' == t_verify_step vsi e);

      (* number of blum evicts is the same as blum adds in the first i entries *)
      lemma_evict_add_count_same_evictedm itsli k;
      assert(MS.size (ts_add_set_key itsli k) = MS.size (ts_evict_set_key itsli k));

      (* the ith element is a blum add *)
      assert(is_blum_add #p (e,tid));
      lemma_ts_add_set_key_extend itsli';
      assert(ts_add_set_key itsli' k == add_elem (ts_add_set_key itsli k)
                                                 (blum_add_elem #p (e,tid)));

      (* the ith element is not a blum evict *)
      assert(not (is_blum_evict (index itsl i)));
      lemma_ts_evict_set_key_extend2 itsli';
      assert(ts_evict_set_key itsli' k == ts_evict_set_key itsli k);

      (* this implies that the size of the add set after processing (i+1) elements
         * is one larger than the evict set at this point *)
      assert(MS.size (ts_add_set_key itsli' k) = 1 + (MS.size (ts_evict_set_key itsli' k)));

      (* this implies that in the first (i+1) entries there is an element whose membership in
         * add multiset is > its membership in evict multiset *)
      let be = diff_elem (ts_add_set_key itsli' k) (ts_evict_set_key itsli' k) in
      lemma_ts_add_set_key_contains_only itsli' k be;
      assert(MH.key_of be = k);

      lemma_mem_key_add_set_same itsli' be;
      lemma_mem_key_evict_set_same itsli' be;
      assert(MS.mem be (ts_add_set itsli') > MS.mem be (ts_evict_set itsli'));

      (* the index of be in the add set *)
      let i_be = some_add_elem_idx itsli' be in
      assert(i_be <= i);

      (* from clock orderedness any evict_set entry for be should happen before i *)
      lemma_evict_before_add2 itsl i_be;
      assert(MS.mem be (ts_evict_set itsl) = MS.mem be (ts_evict_set (prefix itsl i_be)));

      (* any set membership is monotonic *)
      lemma_mem_monotonic be itsl (i + 1);
      lemma_mem_monotonic be itsli' i_be;
      assert(MS.mem be (ts_add_set itsl) >= MS.mem be (ts_add_set itsli'));
      assert(MS.mem be (ts_evict_set itsl) = MS.mem be (ts_evict_set itsli'));

      (* this implies the membership of be in (overall) addset > membership in evict set *)
      (* so these two sets are not equal providing a hash collision *)
      assert(MS.mem be (ts_add_set itsl) > MS.mem be (ts_evict_set itsl));

      MS.lemma_not_equal (ts_add_set itsl) (ts_evict_set itsl) be;
      assert(~( (ts_add_set itsl) == (ts_evict_set itsl)));

      lemma_ts_add_set_correct itsl;
      lemma_ts_evict_set_correct itsl;
      assert(~ (g_add_set gl == g_evict_set gl));

      lemma_g_hadd_correct gl;
      lemma_ghevict_correct gl;

      MultiHashCollision (MSCollision (g_add_seq gl) (g_evict_seq gl))
  )

let lemma_non_eac_evicted_blum_addb (#p:pos)
  (itsl: non_eac_ts_log p{
    VG.hash_verifiable (partition_idx_seq itsl) /\
    EACEvictedBlum? (last_valid_eac_state itsl)  /\
    AddB? (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen =
  (* hash verifiable - evict hash and add hash equal *)
  let gl = partition_idx_seq itsl in

  let st = last_valid_eac_state itsl in
  let ee = invalidating_log_entry itsl in
  match st with
  | EACEvictedBlum v_e t j -> (
    match ee with
    | NEvict (AddB (k, v) t' j') ->
    //assert(v_e <> v || t' <> t || j' <> j);

    let tsle = time_seq_ext itsl in
    let i = max_eac_prefix tsle in
    let (e,tid) = index itsl i in

    let itsli = prefix itsl i in
    (* verifier thread state of tid after itsli *)
    let vsi = verifier_thread_state itsli tid in

    let itsli' = prefix itsl (i + 1) in
    let vsi' = verifier_thread_state itsli' tid in
    lemma_verifier_thread_state_extend itsli';
    //assert(vsi' == t_verify_step vsi e);

    let be = blum_add_elem (index itsl i) in

    (* the previous operation of k is a blum evict *)
    lemma_eac_evicted_blum_implies_previous_evict itsli k;
    let i' = last_idx_of_key itsli k in
    //assert(is_blum_evict (index itsli i'));

    (* since EAC failed, the blum element added to evict set at i' <> blum element added to
     * add set at i *)
    let be' = blum_evict_elem itsli i' in
    //assert(be <> be');

    if MS.contains be (ts_evict_set itsl) then (

      (* since evict set is a set we can identify the unique index that produces be *)
      let j = index_blum_evict itsl be in
      //assert(is_blum_evict (index itsl j));
      //assert(blum_evict_elem itsl j = be);

      (* from clock ordering j has to occur before i *)
      lemma_evict_before_add3 itsl i j;
      //assert (j < i);

      //assert(entry_of_key k (index itsli j));
      lemma_last_index_correct2 (entry_of_key k) itsli j;

      //lemma_index_blum_evict_prefix itsl i i';
      //assert(be' = blum_evict_elem itsli i');
      //assert(blum_evict_elem itsl i' = blum_evict_elem itsli i');
      //assert(j < i');
      //assert(be' = blum_evict_elem itsl i');

      lemma_evict_has_next_add itsli j;
      lemma_blum_evict_add_same itsli j;

      let j' = next_add_of_key itsli j k in
      //assert(blum_add_elem (index itsli j') = be);
      //assert(j' <> i);
      lemma_add_set_mem itsl i j';
      //assert(MS.mem be (ts_add_set itsl) >= 2);

      lemma_ts_add_set_correct itsl;
      //assert(MS.mem be (g_add_set gl) >= 2);
      g_evict_set_is_set gl;
      //assert(is_set (g_evict_set gl));
      //assert(MS.mem be (g_evict_set gl) <= 1);
      MS.lemma_not_equal (g_add_set gl) (g_evict_set gl) be;

      lemma_ghevict_correct gl;
      lemma_g_hadd_correct gl;

      MultiHashCollision (MSCollision (g_add_seq gl) (g_evict_seq gl))
    )
    else (

      lemma_ts_add_set_contains_add_elem itsl i;
      //assert(MS.contains be (ts_add_set itsl));

      MS.lemma_not_equal (ts_add_set itsl) (ts_evict_set itsl) be;
      lemma_ts_evict_set_correct itsl;
      lemma_ts_add_set_correct itsl;
      //assert(~ (g_add_set gl == g_evict_set gl));

      lemma_ghevict_correct gl;
      lemma_g_hadd_correct gl;

      MultiHashCollision (MSCollision (g_add_seq gl) (g_evict_seq gl))
    )
 )
*)



let lemma_non_eac_time_seq_implies_hash_collision
  (itsl: neac_log {VG.hash_verifiable (g_vlog_of itsl)}): hash_collision_gen =
  let i = TL.eac_boundary itsl in
  let st:eac_state = TL.eac_boundary_state_pre itsl in
  let ee:vlog_entry_ext = TL.vlog_entry_ext_at itsl i in

  match st with
  | EACInit -> (
      match ee with
      | NEvict (Get _ _) -> lemma_non_eac_init_requires_key_in_store itsl
      | NEvict (Put _ _) -> lemma_non_eac_init_requires_key_in_store itsl
      | NEvict (AddB _ _ _) -> lemma_non_eac_init_addb itsl
      | NEvict (AddM (k,v) _) -> lemma_non_eac_init_addm itsl
      | EvictMerkle (EvictM _ _) _ -> lemma_non_eac_init_evict itsl
      | EvictBlum (EvictB _ _) _ _ -> lemma_non_eac_init_evict itsl
      | EvictBlum (EvictBM _ _ _) _ _ -> lemma_non_eac_init_evict itsl
    )
  | EACInStore m v -> (
    match ee with
    | NEvict (Get _ _) -> lemma_non_eac_instore_get itsl
    | NEvict (Put _ _) -> lemma_non_eac_instore_put itsl    
    | NEvict (AddB _ _ _) -> lemma_non_eac_instore_addb itsl    
    | NEvict (AddM (k,v) _) -> lemma_non_eac_instore_addm itsl    
    | EvictMerkle (EvictM _ _) _ -> lemma_non_eac_instore_evictm itsl    
    | EvictBlum (EvictB _ _) _ _ -> lemma_non_eac_instore_evictb itsl      
    | EvictBlum (EvictBM _ _ _) _ _ -> lemma_non_eac_instore_evictbm itsl    
    )
  | EACEvictedMerkle v -> (
    match ee with
      | NEvict (Get _ _) -> lemma_non_eac_evicted_requires_key_in_store itsl
      | NEvict (Put _ _) -> lemma_non_eac_evicted_requires_key_in_store itsl      
      | EvictMerkle (EvictM _ _) _ -> lemma_non_eac_evicted_requires_key_in_store itsl
      | EvictBlum (EvictB _ _) _ _ -> lemma_non_eac_evicted_requires_key_in_store itsl   
      | EvictBlum (EvictBM _ _ _) _ _ -> lemma_non_eac_evicted_requires_key_in_store itsl      
      | _ -> admit()
    )
  | EACEvictedBlum v t tid -> (
    match ee with
    | NEvict (Get _ _) -> lemma_non_eac_evicted_requires_key_in_store itsl
      | NEvict (Put _ _) -> lemma_non_eac_evicted_requires_key_in_store itsl          
      | EvictMerkle (EvictM _ _) _ -> lemma_non_eac_evicted_requires_key_in_store itsl
      | EvictBlum (EvictB _ _) _ _ -> lemma_non_eac_evicted_requires_key_in_store itsl   
      | EvictBlum (EvictBM _ _ _) _ _ -> lemma_non_eac_evicted_requires_key_in_store itsl      

    | _ -> admit()
    )
    

(*

  last_valid_eac_state itsl = EACInit /\
                           VT.requires_key_in_store (to_vlog_entry (invalidating_log_entry itsl)) /\
                           Root <> V.key_of (to_vlog_entry (invalidating_log_entry itsl))}):

  let st = last_valid_eac_state itsl in
  let ee = invalidating_log_entry itsl in
  let tsle = time_seq_ext itsl in
  let i = max_eac_prefix tsle in

  match st with
  | EACInit -> (
      match ee with
      | NEvict (Get _ _) -> lemma_non_eac_init_requires_key_in_store itsl
      | NEvict (Put _ _) -> lemma_non_eac_init_requires_key_in_store itsl
      | NEvict (AddB _ _ _) -> lemma_non_eac_init_addb itsl
      | NEvict (AddM (k,v) _) -> lemma_non_eac_init_addm itsl
      | EvictMerkle (EvictM _ _) _ -> lemma_non_eac_init_evict itsl
      | EvictBlum (EvictB _ _) _ _ -> lemma_non_eac_init_evict itsl
      | EvictBlum (EvictBM _ _ _) _ _ -> lemma_non_eac_init_evict itsl
    )
  | EACInStore m v -> (
    match ee with
      | NEvict (Get _ _) -> lemma_non_eac_instore_get itsl
      | NEvict (Put _ _) -> lemma_non_eac_instore_put itsl
      | NEvict (AddB _ _ _) -> lemma_non_eac_instore_addb itsl
      | NEvict (AddM (k,v) _) -> lemma_non_eac_instore_addm itsl
      | EvictMerkle (EvictM _ _) _ -> lemma_non_eac_instore_evictm itsl
      | EvictBlum (EvictB _ _) _ _ -> lemma_non_eac_instore_evictb itsl
      | EvictBlum (EvictBM _ _ _) _ _ -> lemma_non_eac_instore_evictbm itsl
  )
  | EACEvictedMerkle v -> (
    match ee with
      | NEvict (Get _ _) -> lemma_non_eac_evicted_requires_key_in_store itsl
      | NEvict (Put _ _) -> lemma_non_eac_evicted_requires_key_in_store itsl
      | NEvict (AddB _ _ _) ->  lemma_non_eac_evicted_merkle_addb itsl
      | NEvict (AddM (k,v) _) -> lemma_non_eac_evicted_merkle_addm itsl
      | EvictMerkle (EvictM _ _) _ -> lemma_non_eac_evicted_requires_key_in_store itsl
      | EvictBlum (EvictB _ _) _ _ -> lemma_non_eac_evicted_requires_key_in_store itsl
      | EvictBlum (EvictBM _ _ _) _ _ -> lemma_non_eac_evicted_requires_key_in_store itsl
  )
  | EACEvictedBlum v t tid -> (
    match ee with
      | NEvict (Get _ _) -> lemma_non_eac_evicted_requires_key_in_store itsl
      | NEvict (Put _ _) -> lemma_non_eac_evicted_requires_key_in_store itsl
      | NEvict (AddB _ _ _) ->  lemma_non_eac_evicted_blum_addb itsl
      | NEvict (AddM (k,v) _) -> lemma_non_eac_evicted_blum_addm itsl
      | EvictMerkle (EvictM _ _) _ -> lemma_non_eac_evicted_requires_key_in_store itsl
      | EvictBlum (EvictB _ _) _ _ -> lemma_non_eac_evicted_requires_key_in_store itsl
      | EvictBlum (EvictBM _ _ _) _ _ -> lemma_non_eac_evicted_requires_key_in_store itsl
  )
 *)
