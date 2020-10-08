module Veritas.Intermediate.Verifier
open FStar.Integers
open Veritas.Intermediate.Common
module S = Veritas.Intermediate.Store
module MH = Veritas.MultiSetHash
open Veritas.Record
open Veritas.Key

noeq
type vtls =
  | Failed : vtls
  | Valid :
    id : thread_id_t ->
    st : S.vstore ->
    clock : timestamp ->
    hadd : MH.ms_hash_value ->
    hevict : MH.ms_hash_value ->
    vtls

let update_thread_store (vs:vtls {Valid? vs})
                        (st:S.vstore)
                        : vtls =
  match vs with
  | Valid id _ clock hadd hevict -> Valid id st clock hadd hevict

let thread_store (vs:vtls { Valid? vs } )
  : S.vstore
  = Valid?.st vs

let vget (s:slot_id) (v:data_value) (vs: vtls {Valid? vs}): vtls =
  let st = thread_store vs in
  (* check if store contains slot s *)
  if not (S.contains_record st s) then Failed
  (* check if stored value is v *)
  else let Some r = S.get_record st s in
       if not (DVal? r.record_value)
       then Failed
       else if to_data_value r.record_value <> v
       then Failed
       else vs

let vput (s:slot_id) (v:data_value) (vs: vtls {Valid? vs}): vtls =
  let st = thread_store vs in
  (* check if store contains slot s *)
  if not (S.contains_record st s) then Failed
  else update_thread_store vs (S.update_record_value st s (DVal v))

let vaddm (s:slot_id) (r:Veritas.Intermediate.Common.record) (s':slot_id) (vs: vtls {Valid? vs}): vtls =
  let st = thread_store vs in
  if s > Seq.length st then Failed
  //let { record_key = k; record_value = v } = r in
  else let k = r.record_key in
  let v = r.record_value in
  (* the store should contain slot s' *)
  if not (S.contains_record st s') then Failed
  else 
    let Some r' = S.get_record st s' in
    let { 
          record_key = k';
          record_value = v';
          record_add_method = a;
          record_l_child_in_store = l_in_store;
          record_r_child_in_store = r_in_store
        } = r' in 
    (* k should be a proper desc of k' *)
    if not (Veritas.BinTree.is_proper_desc k k') then Failed
    (* the store should not contain slot s *)
    else if S.contains_record st s then Failed
    (* the type of v should be consistent with k *)
    else if not (is_value_of k v) then Failed
    (* v' should be a merkle value *)
    else if DVal? v' then Failed 
    else
      let v' = to_merkle_value v' in
      let d = Veritas.BinTree.desc_dir k k' in
      let dh' = desc_hash_dir v' d in 
      (* check whether k is already in the store *)
      if Veritas.BinTree.Left? d && Desc? dh' && l_in_store then Failed
      else if Veritas.BinTree.Right? d && Desc? dh' && r_in_store then Failed
      else let h = Veritas.Hash.hashfn v in
      match dh' with
      | Empty -> if v = init_value k then
                   let v'_upd = Veritas.Verifier.update_merkle_value v' d k h false in
                   let st_upd = S.update_record_value st s' (MVal v'_upd) in
                   let st_upd2 = S.add_record st_upd s k v Veritas.Verifier.MAdd in
                   update_thread_store vs st_upd2
                 else Failed
      | Desc k2 h2 b2 -> if k2 = k then
                           if h2 = h && b2 = false then
                             update_thread_store vs (S.add_record st s k v Veritas.Verifier.MAdd)
                           else Failed
                         else if v <> init_value k then Failed
                         else if not (Veritas.BinTree.is_proper_desc k2 k) then Failed
                         else
                           let d2 = Veritas.BinTree.desc_dir k2 k in
                           let mv = to_merkle_value v in
                           let mv_upd = Veritas.Verifier.update_merkle_value mv d2 k2 h2 b2 in
                           let v'_upd = Veritas.Verifier.update_merkle_value v' d k h false in
                           let st_upd = S.update_record_value st s' (MVal  v'_upd) in // need to update s' to say that the child in direction d is present
                           let st_upd2 = S.add_record st_upd s k (MVal mv_upd) Veritas.Verifier.MAdd in
                           update_thread_store vs st_upd2


// vevictm

// vaddb

// vevictb

// vevictbm


(* Per invariant.md, we will want to prove something like the following for
   each operation OP above.

High:   hst ----------OP----------> hst'
         ^                           ^
         .                           .
         .                           .
        inv                         inv
         .                           .
         .                           .
         v                           v
Low:    lst ----------OP----------> lst'

  Where hst is the high-level state (Veritas.Verifier.vtls) and lst is the
  low-level state (Veritas.Intermediate.Verifier.vtls).

  We should be able to do this by showing that, during proper execution, 
  Veritas.Intermediate.Store behaves just like a key-value store.


let store_is_map store =
    //1. keys are unique
    (forall s0 s1 in store. store[s0].record_key <> store[s1].record_key) /\
    //2. in store bits unset means that descendent is not in store
    (forall s in store, (d:direction).
         let r = store[s] in
         let dh = descendent d r in
         not (r.in_store d) ==>
         (forall s' in store. store[s'].record_key <> dh.key)) /\
    //3. descendent edges are to the nearest descendent
    (forall s in store, (d:direction).
        let r = store [s] in
        let dh = descendent d r in
        (forall s' in store.
            not (dh.key < store[s'].record_key < r.record_key))

*)
