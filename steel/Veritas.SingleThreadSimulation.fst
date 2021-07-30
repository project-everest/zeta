module Veritas.SingleThreadSimulation
open FStar.Ghost
module I = Veritas.Intermediate.Verify
module S = Veritas.Steel.VerifierModel
module VCache = Veritas.Steel.VCache
module VCfg = Veritas.Intermediate.VerifierConfig
module IStore = Veritas.Intermediate.Store
module MSH = Veritas.MultiSetHashDomain
module U64 = FStar.UInt64
module S_Types = Veritas.Formats.Types
module U16 = FStar.UInt16
module BV = FStar.BV
module L = FStar.List.Tot
module BinTree = Veritas.BinTree


let lemma_seq_to_list_append #a (s0 s1:Seq.seq a)
  : Lemma (Seq.seq_to_list (Seq.append s0 s1) ==
           L.(Seq.seq_to_list s0 @ Seq.seq_to_list s1))
  = admit()

let bv_of_u256 (i:S_Types.u256) : BV.bv_t 256 =
  let open S_Types in
  let open L in
  let bv0 = BV.bv2list (BV.int2bv #64 (U64.v (i.v0))) in
  let bv1 = BV.bv2list (BV.int2bv #64 (U64.v (i.v1))) in
  let bv2 = BV.bv2list (BV.int2bv #64 (U64.v (i.v2))) in
  let bv3 = BV.bv2list (BV.int2bv #64 (U64.v (i.v3))) in
  BV.list2bv (bv0@bv1@bv2@bv3)

let bitvec_of_u256 (i:S_Types.u256) : FStar.BitVector.bv_t 256 =
  Seq.seq_of_list (BV.bv2list (bv_of_u256 i))

let int_of_u256 (i:S_Types.u256) : int =
  BV.bv2int (bv_of_u256 i)

let key_as_l256 (s_key:S_Types.key) : l:list bool { L.length l == 256 } =
  BV.bv2list (bv_of_u256 s_key.S_Types.k)

#push-options "--fuel 0 --ifuel 0"
let key_as_list (s_key:S_Types.key)
  : l:list bool {L.length l == U16.v (s_key.S_Types.significant_digits) } &
    m:list bool {L.(l@m == key_as_l256 s_key)}
  = let l256 = Seq.seq_of_list (key_as_l256 s_key) in
    let n = U16.v s_key.S_Types.significant_digits in
    let l, m = Seq.split_eq l256 n in
    let l' = Seq.seq_to_list l in
    let m' = Seq.seq_to_list m in
    Seq.lemma_list_seq_bij (key_as_l256 s_key);
    lemma_seq_to_list_append l m;
    (| l', m' |)
#pop-options

let rec bool_list_as_bin_tree (l:list bool)
  : BinTree.bin_tree_node
  = let open BinTree in
    match l with
    | [] -> Root
    | true :: rest -> LeftChild (bool_list_as_bin_tree rest)
    | false :: rest -> RightChild (bool_list_as_bin_tree rest)

let s_key_as_i_key (s_key:S_Types.key)
  : Veritas.BinTree.bin_tree_node
  = let (| l, m |) = key_as_list s_key in
    bool_list_as_bin_tree l

let related_key (s_key:S_Types.key)
                (i_key:Veritas.Key.key)
  : prop
  = let open S_Types in
    let (| l, m |) = key_as_list s_key in
    bool_list_as_bin_tree l == i_key /\
    L.for_all (( = ) false) m

assume
val related_key_inj (k0 k1:_) (m0 m1:_)
  : Lemma
    (related_key k0 m0 /\
     related_key k1 m1 ==>
     (m0 == m1 <==> k0 == k1))

let related_desc_hash (s_hash:S_Types.descendent_hash)
                      (i_hash:Veritas.Record.desc_hash)
  : prop
  = let open S_Types in
    let open Veritas.Record in
    match s_hash, i_hash with
    | Dh_vnone (), Empty -> True
    | Dh_vsome dhd, Desc k h b ->
      related_key dhd.dhd_key k /\
      bitvec_of_u256 (dhd.dhd_h) == h /\
      Vtrue? dhd.evicted_to_blum == b
    | _ -> False

let related_merkle_value (s_value:S_Types.mval_value)
                         (i_value:Veritas.Record.merkle_value)
  : prop
  = let open Veritas.Record in
    let open S_Types in
    related_desc_hash s_value.l (MkValue?.l i_value) /\
    related_desc_hash s_value.r (MkValue?.r i_value)

let related_data_value (s_value:S_Types.data_value)
                       (i_value:Veritas.Record.data_value)
  : prop
  = let open S_Types in
    let open Veritas.Record in
    match s_value, i_value with
    | Dv_vnone (), Null -> True
    | Dv_vsome s, DValue i -> int_of_u256 s == i
    | _ -> False

let related_value (#k:Veritas.Key.key)
                  (s_value:S_Types.value)
                  (i_value:Veritas.Record.value_type_of k)
  : prop
  = let open S_Types in
    let open Veritas.Record in
    match s_value, i_value with
    | V_mval mv, MVal mv' -> related_merkle_value mv mv'
    | V_dval dv, DVal dv' -> related_data_value dv dv'
    | _ -> False

assume
val related_value_inj (#k0 #k1:Veritas.Key.key)
                      (v0 v1:_)
                      (u0:Veritas.Record.value_type_of k0)
                      (u1:Veritas.Record.value_type_of k1)
  : Lemma
    (related_value v0 u0 /\
     related_value v1 u1 /\
     (v0 == v1 <==> u0 == u1))

let related_add_method (s_am: S_Types.add_method)
                       (i_am: IStore.add_method)
  : prop
  = let open S_Types in
    match s_am, i_am with
    | MAdd, Veritas.Verifier.MAdd -> True
    | BAdd, Veritas.Verifier.BAdd -> True
    | _ -> False

let related_in_store_tag #vcfg
                         (s_in_store_tag: option (S_Types.slot_id))
                         (i_in_store_tag: option (VCfg.slot_id vcfg))
  : prop
  = match s_in_store_tag, i_in_store_tag with
    | None, None -> True
    | Some s, Some i -> U16.v s == i
    | _ -> False

let related_parent_slot #vcfg
                        (s: option (S_Types.slot_id & bool))
                        (p: option (VCfg.slot_id vcfg & Veritas.BinTree.bin_tree_dir))
  : prop
  = match s, p with
    | None, None -> True
    | Some (s, b), Some (i, d) ->
      U16.v s == i /\
      b == Veritas.BinTree.Left? d
    | _ -> False

let related_record #vcfg
                   (s_record:S_Types.record)
                   (i_record:IStore.vstore_entry vcfg)
  : prop
  = let IStore.VStoreE k v am l_in_store r_in_store p = i_record in
    related_key s_record.S_Types.record_key k /\
    related_value s_record.S_Types.record_value v /\
    related_add_method s_record.S_Types.record_add_method am /\
    related_in_store_tag s_record.S_Types.record_l_child_in_store l_in_store /\
    related_in_store_tag s_record.S_Types.record_r_child_in_store r_in_store /\
    related_parent_slot s_record.S_Types.record_parent_slot p

let related_record_opt #vcfg
                       (s_record:option S_Types.record)
                       (i_record:option (IStore.vstore_entry vcfg))
  : prop
  = match s_record, i_record with
    | None, None -> True
    | Some s, Some i -> related_record s i
    | _ -> False

let related_stores #vcfg
                   (s_store:S.contents)
                   (i_store:IStore.vstore vcfg)
  : prop
  = Seq.length s_store == vcfg.VCfg.store_size /\
    (forall (i:nat { i < Seq.length s_store }).
      related_record_opt (Seq.index s_store i) (Seq.index i_store i))

let related_clocks (s_clock:U64.t)
                   (i_clock:MSH.timestamp)
  : prop
  = let open U64 in
    v (s_clock `shift_right` 32ul) == i_clock.MSH.e /\
    v (s_clock `logand` uint_to_t (FStar.UInt.max_int 32)) == i_clock.MSH.c

let related_hashes (s_hash:S.model_hash)
                   (i_hash:MSH.ms_hash_value)
  : prop
  = s_hash == i_hash

let related_states #vcfg
                   (tsm:S.thread_state_model)
                   (vtls:I.vtls vcfg)
  : prop
  = Seq.length tsm.S.model_store == vcfg.VCfg.store_size /\
    (if tsm.S.model_failed then I.Failed? vtls == true
     else (
     I.Valid? vtls /\
     (let I.Valid id st clock hadd hevict = vtls in
      related_stores tsm.S.model_store st /\
      related_clocks tsm.S.model_clock clock /\
      related_hashes tsm.S.model_hadd hadd /\
      related_hashes tsm.S.model_hevict hevict
      )
    ))
module IL = Veritas.Intermediate.Logs
module VC = Veritas.Intermediate.VerifierConfig
let lift_data_value (d:S_Types.data_value)
  : Veritas.Record.data_value
  = let open S_Types in
    let open Veritas.Record in
    match d with
    | Dv_vnone () -> Null
    | Dv_vsome d -> DValue (int_of_u256 d)

let lift_vlog_entry_get_put #vcfg (e:S_Types.vlog_entry_get_put)
  : option (VC.slot_id vcfg &
            Veritas.Key.data_key &
            Veritas.Record.data_value)
  = let open S_Types in
    let i_slot = U16.v e.vegp_s in
    let i_key = s_key_as_i_key e.vegp_k in
    let i_data = lift_data_value e.vegp_v in
    if i_slot >= VC.store_size vcfg
    ||  Veritas.BinTree.depth i_key <> Veritas.Key.key_size
    ||  U16.v e.vegp_k.significant_digits <> Veritas.Key.key_size
    then None
    else Some (i_slot, i_key, i_data)


let lift_log_entry #vcfg (v:S_Types.vlog_entry)
  : option (IL.logS_entry vcfg)
  = let open S_Types in
    let open IL in
    match v with
    | Ve_Get g -> (
      match lift_vlog_entry_get_put #vcfg g with
      | None -> None
      | Some (s, k, d) -> Some (Get_S s k d)
    )

    | Ve_Put g -> (
      match lift_vlog_entry_get_put #vcfg g with
      | None -> None
      | Some (s, k, d) -> Some (Put_S s k d)
    )

    | _ -> None

let related_lift_vlog_entry_get_put #vcfg (e:S_Types.vlog_entry_get_put)
  : Lemma
    (requires Some? (lift_vlog_entry_get_put #vcfg e))
    (ensures (
      let open Veritas.Record in
      let open S_Types in
      let Some (s, k, v) = lift_vlog_entry_get_put #vcfg e in
      related_key e.vegp_k k /\
      related_value #k (V_dval e.vegp_v) (DVal v)
    ))
  = admit()




#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 4"
////////////////////////////////////////////////////////////////////////////////
// VGET
////////////////////////////////////////////////////////////////////////////////
let related_vget (#vcfg: _)
                 (tsm:S.thread_state_model)
                 (vtls:I.vtls vcfg)
                 (v:S_Types.vlog_entry { S_Types.Ve_Get? v })
  : Lemma
    (requires
      Some? (lift_log_entry #vcfg v) /\
      related_states tsm vtls /\
      I.Valid? vtls)
    (ensures (
      let open S_Types in
      let open IL in
      let gp = Ve_Get?._0 v in
      let Some (Get_S s k d) = lift_log_entry #vcfg v in
      (S.vget_model tsm gp.vegp_s gp.vegp_k (V_dval gp.vegp_v))
        `related_states`
      (I.vget s k d vtls)))
   =
    let open Veritas.Record in
    let open S_Types in
    let open IL in
    let open S in
    let gp = Ve_Get?._0 v in
    let Some (Get_S s k d) = lift_log_entry #vcfg v in
    related_lift_vlog_entry_get_put #vcfg gp;
    let tsm' = S.vget_model tsm gp.vegp_s gp.vegp_k (V_dval gp.vegp_v) in
    let vtls' = I.vget s k d vtls in
    let I.Valid id st clock hadd hevict = vtls in
    match model_get_record tsm gp.vegp_s with
    | None -> ()
    | Some r ->
      let Some s = IStore.get_slot st s in
      let kk = IStore.VStoreE?.k s in
      let vv = IStore.VStoreE?.v s in
      assert (related_key (r.S_Types.record_key) kk);
      assert (related_value (r.S_Types.record_value) vv);
      related_key_inj gp.vegp_k (r.S_Types.record_key)
                      k kk;
      related_value_inj #k #kk (V_dval gp.vegp_v)
                        r.S_Types.record_value
                        (DVal d)
                        vv

////////////////////////////////////////////////////////////////////////////////
// VPUT
////////////////////////////////////////////////////////////////////////////////

let related_slots #vcfg  (slot_s:S_Types.slot_id)
                         (slot_i:VC.slot_id vcfg)
  : prop
  = U16.v slot_s == slot_i

let update_entry #vcfg
                 (i_record:IStore.vstore_entry vcfg)
                 (v:Veritas.Record.value_type_of (IStore.VStoreE?.k i_record))
  : IStore.vstore_entry vcfg
  = let IStore.VStoreE kk _ am l_in_store r_in_store p = i_record in
    IStore.VStoreE kk v am l_in_store r_in_store p

let istore_upd_value #vcfg
                     (st:IStore.vstore vcfg)
                     (s:IStore.inuse_slot_id st)
                     (d:Veritas.Record.value_type_of (IStore.stored_key st s))
  : Lemma
    (requires
      Some? (IStore.get_slot st s))
    (ensures (
      let Some e = IStore.get_slot st s in
      IStore.update_value st s d `Seq.equal`
      Seq.upd st s (Some (update_entry e d))))
  = let open IStore in
    let st' = IStore.update_value st s d in
    //just need to trigger a rewrite get_slot into seq.index
    assert (forall i. i <> s ==> get_slot st i == get_slot st' i /\ Seq.index st i == Seq.index st' i)


let related_vput (#vcfg: _)
                 (tsm:S.thread_state_model)
                 (vtls:I.vtls vcfg)
                 (v:S_Types.vlog_entry { S_Types.Ve_Put? v })
  : Lemma
    (requires
      Some? (lift_log_entry #vcfg v) /\
      related_states tsm vtls /\
      I.Valid? vtls)
    (ensures (
      let open S_Types in
      let open IL in
      let gp = Ve_Put?._0 v in
      let Some (Put_S s k d) = lift_log_entry #vcfg v in
      (S.vput_model tsm gp.vegp_s gp.vegp_k (V_dval gp.vegp_v))
        `related_states`
      (I.vput s k d vtls)))
   = let open Veritas.Record in
     let open S_Types in
     let open IL in
     let open S in
     let gp = Ve_Put?._0 v in
     let Some (Put_S s k d) = lift_log_entry #vcfg v in
     related_lift_vlog_entry_get_put #vcfg gp;
     let tsm' = S.vput_model tsm gp.vegp_s gp.vegp_k (V_dval gp.vegp_v) in
     let vtls' = I.vput s k d vtls in
     let I.Valid id st clock hadd hevict = vtls in
     match model_get_record tsm gp.vegp_s with
     | None -> ()
     | Some r ->
       let Some entry = IStore.get_slot st s in
       let IStore.VStoreE kk vv am l_in_store r_in_store p = entry in
       related_key_inj gp.vegp_k (r.S_Types.record_key)
                      k kk;
       if k <> kk then ()
       else istore_upd_value st s (DVal d)

////////////////////////////////////////////////////////////////////////////////
// VADDM
////////////////////////////////////////////////////////////////////////////////
