module Veritas.ThreadStateModel
open FStar.Ghost

module VSeq = Veritas.SeqAux
module I = Veritas.Intermediate.Verify
module VCfg = Veritas.Intermediate.VerifierConfig
module IStore = Veritas.Intermediate.Store
module MSH = Veritas.MultiSetHashDomain
module U64 = FStar.UInt64
module T = Veritas.Formats.Types
module U16 = FStar.UInt16
module BV = FStar.BV
module L = FStar.List.Tot
module BinTree = Veritas.BinTree
#push-options "--using_facts_from '* -FStar.Seq.Properties.slice_slice'"

let slot (n:U16.t) = x:T.slot_id{ U16.v x < U16.v n}
let is_data_key (k:T.key)
  : bool
  = k.T.significant_digits = 256us

let is_root (k:T.key) 
  : bool
  = k.T.significant_digits = 0us

let is_value_of (k:T.key) (v:T.value)
  : bool
  = if is_data_key k then T.V_dval? v else T.V_mval? v

let data_key = k:T.key{ is_data_key k }

type record (n:U16.t) = {
  record_key : T.key;
  record_value : (v:T.value { is_value_of record_key v });
  record_add_method : T.add_method;
  record_l_child_in_store : option (slot n);
  record_r_child_in_store : option (slot n);
  record_parent_slot : option (slot n & bool);
}

let contents (n:U16.t) = Seq.lseq (option (record n)) (U16.v n)
let model_hash = MSH.ms_hash_value

[@@erasable]
noeq
type thread_state_model = {
  model_failed : bool;
  model_store_len : U16.t;
  model_store : contents model_store_len;
  model_clock : U64.t;
  model_hadd : model_hash;
  model_hevict : model_hash;
  model_thread_id: T.thread_id
}

let lemma_seq_to_list_append #a (s0 s1:Seq.seq a)
  : Lemma (Seq.seq_to_list (Seq.append s0 s1) ==
           L.(Seq.seq_to_list s0 @ Seq.seq_to_list s1))
  = admit()

[@@"opaque_to_smt"]
let bv_of_u256 (i:T.u256) : BV.bv_t 256 =
  let open T in
  let open L in
  let bv0 = BV.bv2list (BV.int2bv #64 (U64.v (i.v0))) in
  let bv1 = BV.bv2list (BV.int2bv #64 (U64.v (i.v1))) in
  let bv2 = BV.bv2list (BV.int2bv #64 (U64.v (i.v2))) in
  let bv3 = BV.bv2list (BV.int2bv #64 (U64.v (i.v3))) in
  BV.list2bv (bv0@bv1@bv2@bv3)

[@@"opaque_to_smt"]
let bitvec_of_u256 (i:T.u256) : FStar.BitVector.bv_t 256 =
  Seq.seq_of_list (BV.bv2list (bv_of_u256 i))

let bitvec_of_u256_inj (i j:_)
  : Lemma
    (ensures bitvec_of_u256 i == bitvec_of_u256 j ==>
             i == j)
    [SMTPat (bitvec_of_u256 i);
     SMTPat (bitvec_of_u256 j)]
  = admit()

[@@"opaque_to_smt"]
let int_of_u256 (i:T.u256) : int =
  BV.bv2int (bv_of_u256 i)

[@@"opaque_to_smt"]
let key_as_l256 (s_key:T.key) : l:list bool { L.length l == 256 } =
  BV.bv2list (bv_of_u256 s_key.T.k)

#push-options "--fuel 0 --ifuel 0"
[@@"opaque_to_smt"]
let key_as_list (s_key:T.key)
  : l:list bool {L.length l == U16.v (s_key.T.significant_digits) } &
    m:list bool {L.(l@m == key_as_l256 s_key)}
  = let l256 = Seq.seq_of_list (key_as_l256 s_key) in
    let n = U16.v s_key.T.significant_digits in
    let l, m = Seq.split_eq l256 n in
    let l' = Seq.seq_to_list l in
    let m' = Seq.seq_to_list m in
    Seq.lemma_list_seq_bij (key_as_l256 s_key);
    lemma_seq_to_list_append l m;
    (| l', m' |)
#pop-options

[@@"opaque_to_smt"]
let rec bool_list_as_bin_tree (l:list bool)
  : BinTree.bin_tree_node
  = let open BinTree in
    match l with
    | [] -> Root
    | true :: rest -> LeftChild (bool_list_as_bin_tree rest)
    | false :: rest -> RightChild (bool_list_as_bin_tree rest)

let related_key (s_key:T.key)
                (i_key:Veritas.Key.key)
  = let open T in
    let (| l, m |) = key_as_list s_key in
    bool_list_as_bin_tree l == i_key /\
    L.for_all (( = ) false) m

[@@"opaque_to_smt"]
let lift_key (s:T.key)
  : option (s':Veritas.Key.key{related_key s s'})
  = let open T in
    let (| l, m |) = key_as_list s in
    if L.for_all (( = ) false) m
    then let k = bool_list_as_bin_tree l in
         if BinTree.depth k < Key.key_size
         then Some k
         else None
    else None

let related_key_inj (k0 k1:_) (m0 m1:_)
  : Lemma
    (ensures related_key k0 m0 /\
             related_key k1 m1 ==>
             (m0 == m1 <==> k0 == k1))
    [SMTPat (related_key k0 m0);
     SMTPat (related_key k1 m1)]
  = admit()

let related_desc_hash (s_hash:T.descendent_hash)
                      (i_hash:Veritas.Record.desc_hash)
  = let open T in
    let open Veritas.Record in
    match s_hash, i_hash with
    | Dh_vnone (), Empty -> True
    | Dh_vsome dhd, Desc k h b ->
      related_key dhd.dhd_key k /\
      bitvec_of_u256 (dhd.dhd_h) == h /\
      Vtrue? dhd.evicted_to_blum == b
    | _ -> False

let related_merkle_value (s_value:T.mval_value)
                         (i_value:Veritas.Record.merkle_value)
  = let open Veritas.Record in
    let open T in
    related_desc_hash s_value.l (MkValue?.l i_value) /\
    related_desc_hash s_value.r (MkValue?.r i_value)

let related_data_value (s_value:T.data_value)
                       (i_value:Veritas.Record.data_value)
  = let open T in
    let open Veritas.Record in
    match s_value, i_value with
    | Dv_vnone (), Null -> True
    | Dv_vsome s, DValue i -> int_of_u256 s == i
    | _ -> False

let related_value (s_value:T.value)
                  (i_value:Veritas.Record.value)
  = let open T in
    let open Veritas.Record in
    match s_value, i_value with
    | V_mval mv, MVal mv' -> related_merkle_value mv mv'
    | V_dval dv, DVal dv' -> related_data_value dv dv'
    | _ -> False

let related_value_inj (v0 v1:_)
                      (u0 u1:Veritas.Record.value)
  : Lemma
    (related_value v0 u0 /\
     related_value v1 u1 /\
     (v0 == v1 <==> u0 == u1))
  = admit()

let related_add_method (s_am: T.add_method)
                       (i_am: IStore.add_method)
  = let open T in
    match s_am, i_am with
    | MAdd, Veritas.Verifier.MAdd -> True
    | BAdd, Veritas.Verifier.BAdd -> True
    | _ -> False

let related_in_store_tag #n #vcfg
                         (s_in_store_tag: option (slot n))
                         (i_in_store_tag: option (VCfg.slot_id vcfg))
  = match s_in_store_tag, i_in_store_tag with
    | None, None -> True
    | Some s, Some i -> U16.v s == i
    | _ -> False

let related_parent_slot #n #vcfg
                        (s: option (slot n & bool))
                        (p: option (VCfg.slot_id vcfg & Veritas.BinTree.bin_tree_dir))
  = match s, p with
    | None, None -> True
    | Some (s, b), Some (i, d) ->
      U16.v s == i /\
      b == Veritas.BinTree.Left? d
    | _ -> False

let related_record #n #vcfg
                   (s_record:record n)
                   (i_record:IStore.vstore_entry vcfg)
  = let IStore.VStoreE k v am l_in_store r_in_store p = i_record in
    related_key s_record.record_key k /\
    related_value s_record.record_value v /\
    related_add_method s_record.record_add_method am /\
    related_in_store_tag s_record.record_l_child_in_store l_in_store /\
    related_in_store_tag s_record.record_r_child_in_store r_in_store /\
    related_parent_slot s_record.record_parent_slot p

let related_record_opt #n #vcfg
                       (s_record:option (record n))
                       (i_record:option (IStore.vstore_entry vcfg))
  = match s_record, i_record with
    | None, None -> True
    | Some s, Some i -> related_record s i
    | _ -> False

let related_stores #n #vcfg
                   (s_store:contents n)
                   (i_store:IStore.vstore vcfg)
  = Seq.length s_store == vcfg.VCfg.store_size /\
    (forall (i:nat { i < Seq.length s_store }).
      related_record_opt (Seq.index s_store i) (Seq.index i_store i))

[@@"opaque_to_smt"]
let timestamp_of_clock (s_clock:U64.t)
  : MSH.timestamp
  = let open U64 in
    MSH.MkTimestamp
      (v (s_clock `shift_right` 32ul))
      (v (s_clock `logand` uint_to_t (FStar.UInt.max_int 32)))

let related_clocks (s_clock:U64.t)
                   (i_clock:MSH.timestamp)
  = timestamp_of_clock s_clock == i_clock

let related_hashes (s_hash:model_hash)
                   (i_hash:MSH.ms_hash_value)
  = s_hash == i_hash

let related_thread_id (s_id:T.thread_id)
                      (i_id:Verifier.thread_id)
  = U16.v s_id = i_id

let related_states #vcfg
                   (tsm:thread_state_model)
                   (vtls:I.vtls vcfg)
  = Seq.length tsm.model_store == vcfg.VCfg.store_size /\
    (if tsm.model_failed then I.Failed? vtls == true
     else (
     I.Valid? vtls /\
     (let I.Valid id st clock hadd hevict = vtls in
      related_thread_id tsm.model_thread_id id /\
      related_stores tsm.model_store st /\
      related_clocks tsm.model_clock clock /\
      related_hashes tsm.model_hadd hadd /\
      related_hashes tsm.model_hevict hevict
      )
    ))

module IL = Veritas.Intermediate.Logs
module VC = Veritas.Intermediate.VerifierConfig
let lift_data_value (d:T.data_value)
  : Veritas.Record.data_value
  = let open T in
    let open Veritas.Record in
    match d with
    | Dv_vnone () -> Null
    | Dv_vsome d -> DValue (int_of_u256 d)

let lift_slot #vcfg (s:T.slot_id)
  : option (VC.slot_id vcfg)
  = let open T in
    let i_slot = U16.v s in
    if i_slot >= VC.store_size vcfg
    then None
    else Some i_slot

let related_slots #vcfg  (slot_s:T.slot_id)
                         (slot_i:VC.slot_id vcfg)
  = U16.v slot_s == slot_i


assume
val lift_value (s:T.value)
  : option (Veritas.Record.value)

let lift_record (s:T.record)
  : option Veritas.Record.record
  = let open T in
    match lift_key s.record_key,
          lift_value s.record_value
    with
    | Some k, Some v -> Some (k, v)
    | _ -> None

let lift_vlog_entry_get_put #vcfg (e:T.vlog_entry_get_put)
  : option (VC.slot_id vcfg &
            Veritas.Key.data_key &
            Veritas.Record.data_value)
  = let open T in
    let i_slot = lift_slot #vcfg e.vegp_s in
    let i_key = lift_key e.vegp_k in
    let i_data = lift_data_value e.vegp_v in
    if None? i_slot
    ||  None? i_key
    ||  Veritas.BinTree.depth (Some?.v i_key) <> Veritas.Key.key_size
    ||  U16.v e.vegp_k.significant_digits <> Veritas.Key.key_size
    then None
    else Some (Some?.v i_slot, Some?.v i_key, i_data)

let lift_log_entry #vcfg (v:T.vlog_entry)
  : option (IL.logS_entry vcfg)
  = let open T in
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

    | Ve_AddM addm -> (
      match lift_slot addm.veam_s,
            lift_record addm.veam_r,
            lift_slot addm.veam_s2
      with
      | Some s, Some r, Some s' ->
        Some (AddM_S s r s')
      | _ -> None
    )

    | Ve_AddB addb -> (
      match lift_slot addb.veab_s,
            lift_record addb.veab_r
      with
      | Some s, Some r ->
        Some (AddB_S s r
                     (timestamp_of_clock addb.veab_t)
                     (U16.v addb.veab_j))
      | _ -> None
    )

    | Ve_EvictM evm -> (
      match lift_slot evm.veem_s,
            lift_slot evm.veem_s2
      with
      | Some s, Some s' ->
        Some (EvictM_S s s')
      | _ -> None
    )

    | Ve_EvictB evb -> (
      match lift_slot evb.veeb_s with
      | Some s ->
        Some (EvictB_S s (timestamp_of_clock evb.veeb_t))
      | _ -> None
    )

    | Ve_EvictBM evb -> (
      match lift_slot evb.veebm_s,
            lift_slot evb.veebm_s2
      with
      | Some s, Some s' ->
        Some (EvictBM_S s s' (timestamp_of_clock evb.veebm_t))
      | _ -> None
    )

let rec lift_log_entries #vcfg (es : Seq.seq T.vlog_entry)
  : Tot (sopt:option (IL.logS vcfg){Some? sopt ==> Seq.length (Some?.v sopt) == Seq.length es})
        (decreases Seq.length es) =

  let n = Seq.length es in
  if n = 0 then Some Seq.empty
  else let prefix = VSeq.prefix es (n - 1) in
       let e = Seq.index es (n - 1) in
       let lifted_prefix = lift_log_entries #vcfg prefix in
       match lifted_prefix with
       | None -> None
       | Some lifted_prefix ->
         (match lift_log_entry #vcfg e with
          | None -> None
          | Some e -> Some (Seq.snoc lifted_prefix e))
