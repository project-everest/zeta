module Veritas.SingleThreadSimulation
open FStar.Ghost
module I = Veritas.Intermediate.Verify
module S = Veritas.Steel.VerifierModel
module VCfg = Veritas.Intermediate.VerifierConfig
module IStore = Veritas.Intermediate.Store
module MSH = Veritas.MultiSetHashDomain
module U64 = FStar.UInt64
module S_Types = Veritas.Formats.Types
module U16 = FStar.UInt16
module BV = FStar.BV
module L = FStar.List.Tot
module BinTree = Veritas.BinTree
open Veritas.ThreadStateModel
module IL = Veritas.Intermediate.Logs
module TSM = Veritas.ThreadStateModel
#push-options "--using_facts_from '* -FStar.Seq.Properties.slice_slice'"

let related_lift_vlog_entry_get_put #vcfg (e:S_Types.vlog_entry_get_put)
  : Lemma
    (requires Some? (lift_vlog_entry_get_put #vcfg e))
    (ensures (
      let open Veritas.Record in
      let open S_Types in
      let Some (s, k, v) = lift_vlog_entry_get_put #vcfg e in
      related_key e.vegp_k k /\
      related_value (V_dval e.vegp_v) (DVal v)
    ))
  = let open Veritas.Record in
    let open S_Types in
    let Some (s, k, v) = lift_vlog_entry_get_put #vcfg e in
    assert (related_key e.vegp_k k);
    admit()

let related_desc_dir (b:bool) (d:Veritas.BinTree.bin_tree_dir) =
  b = Veritas.BinTree.Left? d

let related_key_proper_descendent (k0 k1:S_Types.key) (m0 m1:Veritas.Key.key)
  : Lemma
    (requires related_key k0 m0 /\
              related_key k1 m1)
    (ensures (S.is_proper_descendent k0 k1 <==>
              Veritas.BinTree.is_proper_desc m0 m1) /\
             (S.is_proper_descendent k0 k1 ==>
              (related_desc_dir (S.desc_dir k0 k1)
                                (Veritas.BinTree.desc_dir m0 m1))))
    [SMTPat (S.is_proper_descendent k0 k1);
     SMTPat (Veritas.BinTree.is_proper_desc m0 m1)]
  = admit()

let related_desc_hash_dir (v:_) (b:_)
                          (m:_) (d:_)
  : Lemma
    (requires
      related_merkle_value v m /\
      related_desc_dir b d)
    (ensures
      related_desc_hash (S.desc_hash_dir v b)
                        (Veritas.Record.desc_hash_dir m d))
    [SMTPat (S.desc_hash_dir v b);
     SMTPat (Veritas.Record.desc_hash_dir m d)]
  = admit()

let related_hashfn (v:S_Types.value)
                   (m:Veritas.Record.value)
  : Lemma
    (requires related_value v m)
    (ensures related_hashes (bitvec_of_u256 (S.hashfn v))
                            (Veritas.Hash.hashfn m))
  = admit()

let related_init_value (s_k:_) (i_k:_)
  : Lemma
    (requires related_key s_k i_k)
    (ensures related_value (S.init_value s_k) (Veritas.Record.init_value i_k))
  = admit()

let related_lift_log_entry_addm #vcfg (e:S_Types.vlog_entry { S_Types.Ve_AddM? e})
  : Lemma
    (requires Some? (lift_log_entry #vcfg e))
    (ensures (
      let open Veritas.Record in
      let open S_Types in
      let S_Types.Ve_AddM addm = e in
      let Some (IL.AddM_S s r s') = lift_log_entry #vcfg e in
      related_key addm.veam_r.S_Types.record_key (fst r) /\
      related_value addm.veam_r.S_Types.record_value (snd r)
    ))
  = admit()

let points_to_some_slot_related #vcfg (tsm:_)
                                (st:IStore.vstore vcfg)
                                (s:S_Types.slot_id)
                                (b:bool)
                                (d:Veritas.BinTree.bin_tree_dir)
  : Lemma
    (requires
      related_stores tsm.model_store st /\
      Some? (lift_slot #vcfg s) /\
      Veritas.Intermediate.Store.inuse_slot st (Some?.v (lift_slot #vcfg s)) /\
      related_desc_dir b d)
    (ensures
      S.points_to_some_slot tsm s b ==
      IStore.points_to_some_slot st (Some?.v ((lift_slot #vcfg s))) d)
  = admit()

let madd_to_store_related (#vcfg:_) (tsm:_) (st:IStore.vstore vcfg)
    (s_s:S_Types.slot_id)
    (s_k:S_Types.key)
    (s_v:S_Types.value)
    (s_s':S_Types.slot_id)
    (s_d:bool)
    (i_s:IStore.empty_slot_id st)
    (i_k:Veritas.Key.key)
    (i_v:Record.value_type_of i_k)
    (i_s':IStore.merkle_slot_id st)
    (i_d:BinTree.bin_tree_dir)
  : Lemma
    (requires
      related_stores tsm.model_store st /\
      (lift_slot #vcfg s_s == Some i_s) /\
      related_key s_k i_k /\
      related_value s_v i_v /\
      (lift_slot #vcfg s_s' == Some i_s') /\
      related_desc_dir s_d i_d /\
      IStore.points_to_none st i_s' i_d /\
      is_value_of s_k s_v /\
      not (S.has_slot tsm s_s))
    (ensures (
      let tsm' = S.model_madd_to_store tsm s_s s_k s_v s_s' s_d in
      let st'  = IStore.madd_to_store st i_s i_k i_v i_s' i_d in
      related_stores tsm'.model_store st' /\
      tsm' == { tsm with model_store = tsm'.model_store} //modifies only the store
      ))
  = admit()

let madd_to_store_split_related (#vcfg:_) (tsm:_) (st:IStore.vstore vcfg)
    (s_s:S_Types.slot_id)
    (s_k:S_Types.key)
    (s_v:S_Types.value)
    (s_s':S_Types.slot_id)
    (s_d:bool)
    (s_d2:bool)
    (i_s:IStore.empty_slot_id st)
    (i_k:Veritas.Key.key)
    (i_v:Record.value_type_of i_k)
    (i_s':IStore.merkle_slot_id st)
    (i_d:BinTree.bin_tree_dir)
    (i_d2:BinTree.bin_tree_dir)
  : Lemma
    (requires
      related_stores tsm.model_store st /\
      (lift_slot #vcfg s_s == Some i_s) /\
      related_key s_k i_k /\
      related_value s_v i_v /\
      (lift_slot #vcfg s_s' == Some i_s') /\
      related_desc_dir s_d i_d /\
      IStore.points_to_some_slot st i_s' i_d /\
      is_value_of s_k s_v /\
      not (S.has_slot tsm s_s))
    (ensures (
      let tsm' = S.model_madd_to_store_split tsm s_s s_k s_v s_s' s_d s_d2 in
      let st'  = IStore.madd_to_store_split st i_s i_k i_v i_s' i_d i_d2 in
      related_stores tsm'.model_store st' /\
      tsm' == { tsm with model_store = tsm'.model_store} //modifies only the store
      ))
  = admit()

let mevict_from_store_related (#vcfg:_) (tsm:_) (st:IStore.vstore vcfg)
    (s_s:S_Types.slot_id)
    (s_s':S_Types.slot_id)
    (s_d:bool)
    (i_s:IStore.inuse_slot_id st)
    (i_s':IStore.inuse_slot_id st { i_s <> i_s' })
    (i_d:BinTree.bin_tree_dir)
  : Lemma
    (requires
      related_stores tsm.model_store st /\
      (lift_slot #vcfg s_s == Some i_s) /\
      (lift_slot #vcfg s_s' == Some i_s') /\
      related_desc_dir s_d i_d /\
      IStore.points_to_none st i_s BinTree.Left /\
      IStore.points_to_none st i_s BinTree.Right /\
      ((not (IStore.has_parent st i_s) /\
       IStore.points_to_none st i_s' i_d)
       \/
       (IStore.has_parent st i_s /\
        IStore.parent_slot st i_s = i_s' /\
        IStore.parent_dir st i_s = i_d)))
    (ensures (
      let tsm' = S.model_mevict_from_store tsm s_s s_s' s_d in
      let st'  = IStore.mevict_from_store st i_s i_s' i_d in
      related_stores tsm'.model_store st' /\
      tsm' == { tsm with model_store = tsm'.model_store} //modifies only the store
      ))
    [SMTPat (S.model_mevict_from_store tsm s_s s_s' s_d);
     SMTPat (IStore.mevict_from_store st i_s i_s' i_d)]
  = admit()

let bevict_from_store_related (#vcfg:_) (tsm:_) (st:IStore.vstore vcfg)
    (s_s:S_Types.slot_id)
    (i_s:IStore.inuse_slot_id st)
  : Lemma
    (requires
      related_stores tsm.model_store st /\
      (lift_slot #vcfg s_s == Some i_s) /\
      IStore.points_to_none st i_s BinTree.Left /\
      IStore.points_to_none st i_s BinTree.Right /\
      IStore.add_method_of st i_s == Verifier.BAdd)
    (ensures (
      let tsm' = S.model_bevict_from_store tsm s_s in
      let st'  = IStore.bevict_from_store st i_s in
      related_stores tsm'.model_store st' /\
      tsm' == { tsm with model_store = tsm'.model_store} //modifies only the store
      ))
    [SMTPat (S.model_bevict_from_store tsm s_s);
     SMTPat (IStore.bevict_from_store st i_s)]
  = admit()

let related_update_merkle_value (s_v:_)
                                (s_d:_)
                                (s_k:_)
                                (s_h:_)
                                (i_v:_)
                                (i_d:_)
                                (i_k:_)
                                (i_h:_)
                                (b:bool)
  : Lemma
    (requires
      related_merkle_value s_v i_v /\
      related_desc_dir s_d i_d /\
      related_key s_k i_k /\
      related_hashes (bitvec_of_u256 s_h) i_h
  )
    (ensures
      related_merkle_value
        (S.update_merkle_value s_v s_d s_k s_h b)
        (Verifier.update_merkle_value i_v i_d i_k i_h b))
    [SMTPat (S.update_merkle_value s_v s_d s_k s_h b);
     SMTPat (Verifier.update_merkle_value i_v i_d i_k i_h b)]
  = admit()

let value_of_related (s_k:_) (s_v:_)
                     (i_k:_) (i_v:_)
  : Lemma
    (requires
      related_key s_k i_k /\
      related_value s_v i_v)
    (ensures
      TSM.is_value_of s_k s_v <==>
      Record.is_value_of i_k i_v)
  = admit()

let related_lift_log_entry_addb #vcfg (e:S_Types.vlog_entry { S_Types.Ve_AddB? e})
  : Lemma
    (requires Some? (lift_log_entry #vcfg e))
    (ensures (
      let open Veritas.Record in
      let open S_Types in
      let S_Types.Ve_AddB addb = e in
      let Some (IL.AddB_S s r t j) = lift_log_entry #vcfg e in
      related_key addb.veab_r.S_Types.record_key (fst r) /\
      related_value addb.veab_r.S_Types.record_value (snd r) /\
      related_clocks addb.veab_t t
    ))
  = admit()

let update_hadd_related #vcfg (tsm:_) (vtls:I.vtls vcfg)
                              (s_r:S_Types.record)
                              (s_t:S_Types.timestamp)
                              (s_j:S_Types.thread_id)
                              (i_r:Record.record)
  : Lemma
    (requires
      I.Valid? vtls /\
      related_states tsm vtls /\
      related_key s_r.S_Types.record_key (fst i_r) /\
      related_value s_r.S_Types.record_value (snd i_r))
    (ensures (
      let i_t = timestamp_of_clock s_t in
      let i_j = U16.v s_j in
      let tsm' = S.model_update_hadd tsm s_r s_t s_j in
      let vtls' =
        let h_upd = MultiSetHash.ms_hashfn_upd (MSH.MHDom i_r i_t i_j) (I.thread_hadd vtls) in
        I.update_thread_hadd vtls h_upd
      in
      related_states tsm' vtls'))
  = admit()

let update_clock_related #vcfg (tsm:_) (vtls:I.vtls vcfg)
                               (s_t:S_Types.timestamp)
  : Lemma
    (requires
      I.Valid? vtls /\
      related_states tsm vtls)
    (ensures (
      let i_t = timestamp_of_clock s_t in
      let tsm' = S.model_update_clock tsm s_t in
      let vtls' =
        let clk = I.thread_clock vtls in
        let clk_upd = Verifier.max clk (MSH.next i_t) in
        I.update_thread_clock vtls clk_upd
      in
      related_states tsm' vtls'))
  = admit()

let badd_to_store_related #vcfg (tsm:_) (vtls:I.vtls vcfg{I.Valid? vtls})
                                (s_s:_) (s_k:_) (s_v:_)
                                (i_s:VCfg.slot_id vcfg) (i_k:_) (i_v:_)
  : Lemma
    (requires
      I.Valid? vtls /\
      related_states tsm vtls /\
      related_slots #vcfg s_s i_s /\
      related_key s_k i_k /\
      related_value s_v i_v /\
      not (IStore.inuse_slot (I.thread_store vtls) i_s))
    (ensures (
      let tsm' = S.(model_put_record tsm s_s (mk_record s_k s_v S_Types.BAdd)) in
      let st = I.thread_store vtls in
      let vtls' = I.update_thread_store vtls (IStore.badd_to_store st i_s i_k i_v) in
      related_states tsm' vtls'))
  = admit()

let timestamp_lt_related_aux  (s_t s_t':S_Types.timestamp)
                              (i_t i_t':MSH.timestamp)
  : Lemma
    (requires
      related_clocks s_t i_t /\
      related_clocks s_t' i_t' /\
      MSH.ts_lt i_t i_t')
    (ensures S.timestamp_lt s_t s_t')
  = let open U64 in
    reveal_opaque (`%timestamp_of_clock) timestamp_of_clock;
    assert (i_t == MSH.MkTimestamp (v (s_t `shift_right` 32ul))
                                   (v (s_t `logand` uint_to_t (FStar.UInt.max_int 32))));
    assert (i_t' == MSH.MkTimestamp (v (s_t' `shift_right` 32ul))
                                    (v (s_t' `logand` uint_to_t (FStar.UInt.max_int 32))));
    if ((s_t `shift_right` 32ul) `lt` (s_t' `shift_right` 32ul))
    then begin
      assert (v (s_t `shift_right` 32ul) == v s_t / pow2 32);
      assert (v (s_t' `shift_right` 32ul) == v s_t' / pow2 32)
    end
    else begin
      assert (v (s_t `shift_right` 32ul) ==
              v (s_t' `shift_right` 32ul));
      assert (v (s_t `logand` uint_to_t (FStar.UInt.max_int 32)) <
              v (s_t' `logand` uint_to_t (FStar.UInt.max_int 32)));
      admit ()
    end

let timestamp_lt_related  (s_t s_t':S_Types.timestamp)
                          (i_t i_t':MSH.timestamp)
  : Lemma
    (requires
      related_clocks s_t i_t /\
      related_clocks s_t' i_t')
    (ensures
      MSH.ts_lt i_t i_t' <==>
      S.timestamp_lt s_t s_t')
    [SMTPat (related_clocks s_t i_t);
     SMTPat (related_clocks s_t' i_t')]
  = admit()

let is_root_related (s_k:_) (i_k:Veritas.Key.key)
  : Lemma
    (requires
      related_key s_k i_k)
    (ensures
      is_root s_k <==> i_k=BinTree.Root)
    [SMTPat (related_key s_k i_k);
     SMTPat (is_root s_k)]
  = admit()

let model_update_hash_related (s_h:_) (s_k:_) (s_v:_) (s_t:_) (s_j:_)
                              (i_h:_) (i_k:_) (i_v:_) (i_t:_) (i_j:_)
  : Lemma
    (requires
      related_hashes s_h i_h /\
      related_key s_k i_k /\
      related_value s_v i_v /\
      related_thread_id s_j i_j /\
      related_clocks s_t i_t)
    (ensures (
      let open S_Types in
      related_hashes
        (S.model_update_hash s_h ({record_key=s_k; record_value=s_v}) s_t s_j)
        (MultiSetHash.ms_hashfn_upd (MSH.MHDom (i_k, i_v) i_t i_j) i_h)))
    [SMTPat (S.model_update_hash s_h ({S_Types.record_key=s_k; S_Types.record_value=s_v}) s_t s_j);
    SMTPat (MultiSetHash.ms_hashfn_upd (MSH.MHDom (i_k, i_v) i_t i_j) i_h)]
  = admit()


#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 4"
////////////////////////////////////////////////////////////////////////////////
// VGET
////////////////////////////////////////////////////////////////////////////////
let related_vget (#vcfg: _)
                 (tsm:thread_state_model)
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
      (S.vget_model tsm gp.vegp_s gp.vegp_k gp.vegp_v)
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
    let tsm' = S.vget_model tsm gp.vegp_s gp.vegp_k gp.vegp_v in
    let vtls' = I.vget s k d vtls in
    let I.Valid id st clock hadd hevict = vtls in
    match model_get_record tsm gp.vegp_s with
    | None -> ()
    | Some r ->
      let Some s = IStore.get_slot st s in
      let kk = IStore.VStoreE?.k s in
      let vv = IStore.VStoreE?.v s in
      assert (related_key (r.TSM.record_key) kk);
      assert (related_value (r.TSM.record_value) vv);
      related_key_inj gp.vegp_k (r.TSM.record_key)
                      k kk;
      related_value_inj (V_dval gp.vegp_v)
                        r.TSM.record_value
                        (DVal d)
                        vv

////////////////////////////////////////////////////////////////////////////////
// VPUT
////////////////////////////////////////////////////////////////////////////////


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
    [SMTPat (IStore.update_value st s d)]
  = let open IStore in
    let st' = IStore.update_value st s d in
    //just need to trigger a rewrite get_slot into seq.index
    assert (forall i. i <> s ==> get_slot st i == get_slot st' i /\ Seq.index st i == Seq.index st' i)

let related_vput (#vcfg: _)
                 (tsm:TSM.thread_state_model)
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
      (S.vput_model tsm gp.vegp_s gp.vegp_k gp.vegp_v)
        `related_states`
      (I.vput s k d vtls)))
   = let open Veritas.Record in
     let open S_Types in
     let open IL in
     let open S in
     let gp = Ve_Put?._0 v in
     let Some (Put_S s k d) = lift_log_entry #vcfg v in
     related_lift_vlog_entry_get_put #vcfg gp;
     let tsm' = S.vput_model tsm gp.vegp_s gp.vegp_k gp.vegp_v in
     let vtls' = I.vput s k d vtls in
     let I.Valid id st clock hadd hevict = vtls in
     match model_get_record tsm gp.vegp_s with
     | None -> ()
     | Some r ->
       let Some entry = IStore.get_slot st s in
       let IStore.VStoreE kk vv am l_in_store r_in_store p = entry in
       related_key_inj gp.vegp_k (r.TSM.record_key)
                      k kk;
       if k <> kk then ()
       else istore_upd_value st s (DVal d)

////////////////////////////////////////////////////////////////////////////////
// VADDM
////////////////////////////////////////////////////////////////////////////////
#push-options "--z3rlimit_factor 8 --ifuel 1"

let vaddm_basic_preconditions tsm s_s s_k s_v s_s' s_k' s_v'
                              s_mv' s_d s_dh' s_h
                              #vcfg (vtls:I.vtls vcfg{I.Valid? vtls})
                              i_s i_k i_v i_s' i_k' i_v'
                              i_mv' i_d i_dh' i_h
  = let st = (I.thread_store vtls) in
    related_states tsm vtls /\
    related_slots #vcfg s_s i_s /\
    related_key s_k i_k /\
    related_value s_v i_v /\
    related_slots #vcfg s_s' i_s' /\
    related_key s_k' i_k' /\
    related_value s_v' i_v' /\
    (S.is_proper_descendent s_k s_k' /\
     Some? (S.model_get_record tsm s_s') /\
     TSM.is_value_of s_k s_v /\
     (let r = Some?.v (S.model_get_record tsm s_s') in
      r.record_key == s_k' /\
      r.record_value == s_v') /\
    Some s_mv' == S.to_merkle_value s_v' /\
    s_d == S.desc_dir s_k s_k' /\
    s_dh' == S.desc_hash_dir s_mv' s_d /\
    s_h == S.hashfn s_v) /\
    (i_s <> i_s' /\
     not (IStore.empty_slot st i_s') /\
     BinTree.is_proper_desc i_k i_k' /\
     not (IStore.inuse_slot st i_s) /\
     Record.is_value_of i_k i_v /\
     IStore.stored_key st i_s' == i_k' /\
     IStore.stored_value st i_s' == i_v' /\
     i_mv'== Veritas.Record.to_merkle_value i_v' /\
     i_d == Veritas.BinTree.desc_dir i_k i_k' /\
     i_dh' == Veritas.Record.desc_hash_dir i_mv' i_d /\
     i_h == Veritas.Hash.hashfn i_v)

let related_vaddm_no_child tsm s_s s_k s_v s_s' s_k' s_v' s_mv' s_d s_dh' s_h
                           #vcfg (vtls:I.vtls vcfg{I.Valid? vtls})
                           i_s i_k i_v i_s' i_k' i_v' i_mv' i_d i_dh' i_h
  : Lemma
    (requires vaddm_basic_preconditions
                   tsm s_s s_k s_v s_s' s_k' s_v'
                   s_mv' s_d s_dh' s_h
                   vtls i_s i_k i_v i_s' i_k' i_v'
                   i_mv' i_d i_dh' i_h /\
              S_Types.Dh_vnone? s_dh')
    (ensures
      (S.vaddm_model tsm s_s S_Types.({record_key = s_k; record_value = s_v}) s_s'
        `related_states`
      (I.vaddm i_s (i_k, i_v) i_s' vtls)))
  = let open Veritas.Record in
    let open S_Types in
    let open IL in
    let open S in
    related_key_proper_descendent s_k s_k' i_k i_k';
    let tsm' =
      S.vaddm_model
        tsm
        s_s
        S_Types.({record_key = s_k; record_value = s_v})
        s_s'
    in
    let vtls' = I.vaddm i_s (i_k, i_v) i_s' vtls in
    let st = (I.thread_store vtls) in
    let s_r' = Some?.v (S.model_get_record tsm s_s') in
    let Some i_r' = IStore.get_slot st i_s' in
    related_hashfn s_v i_v;
    related_desc_hash_dir s_mv' s_d i_mv' i_d;
    assert (i_dh' == Empty);
    related_init_value s_k i_k;
    if s_v = S.init_value s_k
    then (
      assert (i_v = Veritas.Record.init_value i_k);
      points_to_some_slot_related tsm st s_s' s_d i_d;
      if S.points_to_some_slot tsm s_s' s_d
      then ()
      else (
        madd_to_store_related tsm st s_s s_k s_v s_s' s_d i_s i_k i_v i_s' i_d;
        let tsm1 = S.model_madd_to_store tsm s_s s_k s_v s_s' s_d in
        let st1 = IStore.madd_to_store st i_s i_k i_v i_s' i_d in
        assert (related_stores tsm1.model_store st1);

        related_update_merkle_value
                  (S_Types.V_mval?._0 s_v') s_d s_k s_h
                  (Record.MVal?.v i_v') i_d i_k i_h false
      )
    )
    else (
      assert (i_v <> Veritas.Record.init_value i_k)
    )

let related_vaddm_some_child tsm s_s s_k s_v s_s' s_k' s_v' s_mv' s_d s_dh' s_h
                           #vcfg (vtls:I.vtls vcfg{I.Valid? vtls})
                           i_s i_k i_v i_s' i_k' i_v' i_mv' i_d i_dh' i_h
  : Lemma
    (requires vaddm_basic_preconditions
                   tsm s_s s_k s_v s_s' s_k' s_v'
                   s_mv' s_d s_dh' s_h
                   vtls i_s i_k i_v i_s' i_k' i_v'
                   i_mv' i_d i_dh' i_h /\
              S_Types.Dh_vsome? s_dh')
    (ensures
      (S.vaddm_model tsm s_s S_Types.({record_key = s_k; record_value = s_v}) s_s'
        `related_states`
      (I.vaddm i_s (i_k, i_v) i_s' vtls)))
  = let open Veritas.Record in
    let open S_Types in
    let open IL in
    let open S in
    related_key_proper_descendent s_k s_k' i_k i_k';
    let tsm' =
      S.vaddm_model
        tsm
        s_s
        S_Types.({record_key = s_k; record_value = s_v})
        s_s'
    in
    let vtls' = I.vaddm i_s (i_k, i_v) i_s' vtls in
    let st = (I.thread_store vtls) in
    let s_r' = Some?.v (S.model_get_record tsm s_s') in
    let Some i_r' = IStore.get_slot st i_s' in
    related_hashfn s_v i_v;
    related_desc_hash_dir s_mv' s_d i_mv' i_d;
    let Dh_vsome {dhd_key=s_k2; dhd_h=s_h2; evicted_to_blum = s_b2} = s_dh' in
    let Desc i_k2 i_h2 i_b2 = i_dh' in
    related_key_inj s_k s_k2 i_k i_k2;
    if s_k2 = s_k
    then (
       points_to_some_slot_related tsm st s_s' s_d i_d;
       if not (s_h2 = s_h && s_b2 = Vfalse)
       then ()
       else if points_to_some_slot tsm s_s' s_d
       then ()
       else (
         madd_to_store_related tsm st s_s s_k s_v s_s' s_d i_s i_k i_v i_s' i_d
       )
    )
    else (
      related_init_value s_k i_k;
      if s_v <> S.init_value s_k
      then ()
      else (
        related_key_proper_descendent s_k2 s_k i_k2 i_k;
        if not (S.is_proper_descendent s_k2 s_k)
        then ()
        else (
          let Some s_mv = S.to_merkle_value s_v in
          let s_d2 = S.desc_dir s_k2 s_k in
          let Record.MVal i_mv = i_v in
          let i_d2 = BinTree.desc_dir i_k2 i_k in
          assert (related_desc_dir s_d2 i_d2);
          related_update_merkle_value
            s_mv s_d2 s_k2 s_h2
            i_mv i_d2 i_k2 i_h2 i_b2;
          let i_mv_upd = Verifier.update_merkle_value i_mv i_d2 i_k2 i_h2 i_b2 in
          let s_mv_upd = S.update_merkle_value s_mv s_d2 s_k2 s_h2 (s_b2=Vtrue) in
          related_update_merkle_value
            s_mv' s_d s_k s_h
            i_mv' i_d i_k i_h false;
          let i_v'_upd = Verifier.update_merkle_value i_mv' i_d i_k i_h false in
          let s_v'_upd = S.update_merkle_value s_mv' s_d s_k s_h false in
          points_to_some_slot_related
            tsm st s_s' s_d i_d;
          if S.points_to_some_slot tsm s_s' s_d
          then
            madd_to_store_split_related tsm st
              s_s s_k (V_mval s_mv_upd) s_s' s_d s_d2
              i_s i_k (MVal i_mv_upd) i_s' i_d i_d2
          else
            madd_to_store_related tsm st
               s_s s_k (V_mval s_mv_upd) s_s' s_d
               i_s i_k (MVal i_mv_upd) i_s' i_d
        )
      )
    )


let related_vaddm (#vcfg: _)
                  (tsm:TSM.thread_state_model)
                  (vtls:I.vtls vcfg)
                  (v:S_Types.vlog_entry)
  : Lemma
    (requires
      S_Types.Ve_AddM? v == true /\
      Some? (lift_log_entry #vcfg v) == true /\
      related_states tsm vtls /\
      I.Valid? vtls == true)
    (ensures (
      let open S_Types in
      let open IL in
      let addm = Ve_AddM?._0 v in
      let Some (AddM_S s r s') = lift_log_entry #vcfg v in
      (S.vaddm_model tsm addm.veam_s addm.veam_r addm.veam_s2
        `related_states`
      (I.vaddm s r s' vtls))))
  = let open Veritas.Record in
    let open S_Types in
    let open IL in
    let open S in
    let addm = Ve_AddM?._0 v in
    let Some (AddM_S i_s i_r i_s') = lift_log_entry #vcfg v in
    related_lift_log_entry_addm #vcfg v;
    let s_s = addm.veam_s in
    let s_r = addm.veam_r in
    let s_s' = addm.veam_s2  in
    let tsm' = S.vaddm_model tsm s_s s_r s_s' in
    let vtls' = I.vaddm i_s i_r i_s' vtls in
    let I.Valid id st clock hadd hevict = vtls in
    match model_get_record tsm s_s' with
    | None -> ()
    | Some s_r' ->
      assert (not (IStore.empty_slot st i_s'));
      let Some i_r' = IStore.get_slot st i_s' in
      assert (related_record s_r' i_r');
      let s_k = addm.veam_r.S_Types.record_key in
      let s_v = addm.veam_r.S_Types.record_value in
      let s_k' = s_r'.TSM.record_key in
      let s_v' = s_r'.TSM.record_value in
      let i_k, i_v = i_r in
      let i_k' = IStore.stored_key st i_s' in
      let i_v' = IStore.stored_value st i_s' in
      if i_s = i_s'
      then (
        assert (vtls' == I.Failed);
        assert (tsm'.model_failed)
        //At the TSM level, we do not explicitly check that s <> s'
        //but it follows anyway, since if s' is not in the store it fails
        //and if s' is in the store then s must not be in the store
      ) else (
        related_key_proper_descendent s_k s_k' i_k i_k';
        if not (S.is_proper_descendent s_k s_k')
        then ()
        else if Some? (model_get_record tsm s_s)
        then ()
        else (
          value_of_related s_k s_v i_k i_v;
          if not (TSM.is_value_of s_k s_v)
          then ()
          else (
            assert (Veritas.Record.is_value_of i_k i_v);
            assert (Veritas.Record.MVal? i_v');
            assert (related_value s_v' i_v');
            assert (S_Types.V_mval? s_v');
            let i_mv' = Veritas.Record.to_merkle_value i_v' in
            let i_d = Veritas.BinTree.desc_dir i_k i_k' in
            let i_dh' = Veritas.Record.desc_hash_dir i_mv' i_d in
            let i_h = Veritas.Hash.hashfn i_v in
            let Some s_mv' = S.to_merkle_value s_v' in
            let s_d = S.desc_dir s_k s_k' in
            let s_dh' = S.desc_hash_dir s_mv' s_d in
            let s_h = S.hashfn s_v in
            related_hashfn s_v i_v;
            assert (related_hashes (bitvec_of_u256 s_h) i_h);
            related_desc_hash_dir s_mv' s_d i_mv' i_d;
            match s_dh' with
            | S_Types.Dh_vnone _ ->
              related_vaddm_no_child
                tsm s_s s_k s_v s_s' s_k' s_v' s_mv' s_d s_dh' s_h
              vtls i_s i_k i_v i_s' i_k' i_v' i_mv' i_d i_dh' i_h
            | _ ->
              related_vaddm_some_child
                tsm s_s s_k s_v s_s' s_k' s_v' s_mv' s_d s_dh' s_h
              vtls i_s i_k i_v i_s' i_k' i_v' i_mv' i_d i_dh' i_h
          )
        )
      )

////////////////////////////////////////////////////////////////////////////////
// vaddb
////////////////////////////////////////////////////////////////////////////////

let related_vaddb (#vcfg: _)
                  (tsm:TSM.thread_state_model)
                  (vtls:I.vtls vcfg)
                  (v:S_Types.vlog_entry)
  : Lemma
    (requires
      S_Types.Ve_AddB? v == true /\
      Some? (lift_log_entry #vcfg v) == true /\
      related_states tsm vtls /\
      I.Valid? vtls == true)
    (ensures (
      let open S_Types in
      let open IL in
      let addb = Ve_AddB?._0 v in
      let Some (AddB_S s r t j) = lift_log_entry #vcfg v in
      (S.vaddb_model tsm addb.veab_s addb.veab_r addb.veab_t addb.veab_j
        `related_states`
      (I.vaddb s r t j vtls))))
  = let open S_Types in
    let open IL in
    let addb = Ve_AddB?._0 v in
    let s_s = addb.veab_s in
    let s_r = addb.veab_r in
    let s_k = s_r.record_key in
    let s_v = s_r.record_value in
    let s_t = addb.veab_t in
    let s_j = addb.veab_j in
    let Some (AddB_S i_s i_r i_t i_j) = lift_log_entry #vcfg v in
    let tsm' = S.vaddb_model tsm s_s s_r s_t s_j in
    let vtls' = I.vaddb i_s i_r i_t i_j vtls in
    let i_k, i_v = i_r in
    related_lift_log_entry_addb #vcfg v;
    value_of_related s_k s_v i_k i_v;
    if not (TSM.is_value_of s_k s_v) then ()
    else if Some? (S.model_get_record tsm s_s) then ()
    else (
      update_hadd_related tsm vtls s_r s_t s_j i_r;
      update_clock_related tsm vtls s_t;
      badd_to_store_related tsm vtls s_s s_k s_v i_s i_k i_v
    )

////////////////////////////////////////////////////////////////////////////////
// vevictm
////////////////////////////////////////////////////////////////////////////////

let related_vevictm (#vcfg: _)
                    (tsm:TSM.thread_state_model)
                    (vtls:I.vtls vcfg)
                    (v:S_Types.vlog_entry)
  : Lemma
    (requires
      S_Types.Ve_EvictM? v == true /\
      Some? (lift_log_entry #vcfg v) == true /\
      related_states tsm vtls /\
      I.Valid? vtls == true)
    (ensures (
      let open S_Types in
      let open IL in
      let { veem_s = s_s; veem_s2 = s_s'} = Ve_EvictM?._0 v in
      let Some (EvictM_S i_s i_s') = lift_log_entry #vcfg v in
      S.vevictm_model tsm s_s s_s'
        `related_states`
      I.vevictm i_s i_s' vtls))
  = let open S_Types in
    let open IL in
    let { veem_s = s_s; veem_s2 = s_s'} = Ve_EvictM?._0 v in
    let Some (EvictM_S i_s i_s') = lift_log_entry #vcfg v in
    let tsm' = S.vevictm_model tsm s_s s_s' in
    let vtls' = I.vevictm i_s i_s' vtls in
      match S.model_get_record tsm s_s,
            S.model_get_record tsm s_s'
      with
      | Some s_r, Some s_r' ->
        let s_k = s_r.TSM.record_key in
        let s_v = s_r.TSM.record_value in
        let s_k' = s_r'.TSM.record_key in
        let s_v' = s_r'.TSM.record_value in
        let st = I.thread_store vtls in
        let i_k = IStore.stored_key st i_s in
        let i_v = IStore.stored_value st i_s in
        let i_k' = IStore.stored_key st i_s' in
        let i_v' = IStore.stored_value st i_s' in
        related_key_proper_descendent s_k s_k' i_k i_k';
        points_to_some_slot_related tsm st s_s true BinTree.Left;
        points_to_some_slot_related tsm st s_s false BinTree.Right;
        if not (S.is_proper_descendent s_k s_k')
        || S.points_to_some_slot tsm s_s true
        || S.points_to_some_slot tsm s_s false
        then ()
        else (
          let s_d = S.desc_dir s_k s_k' in
          let s_h = S.hashfn s_v in
          let i_d = BinTree.desc_dir i_k i_k' in
          let i_h = Hash.hashfn i_v in
          related_hashfn s_v i_v;
          assert (related_desc_dir s_d i_d);
          let Some s_mv' = S.to_merkle_value s_v' in
          let i_mv' = Record.to_merkle_value i_v' in
          let s_dh' = S.desc_hash_dir s_mv' s_d in
          let i_dh' = Record.desc_hash_dir i_mv' i_d in
          related_desc_hash_dir s_mv' s_d i_mv' i_d;
          match s_dh' with
          | Dh_vnone _ -> ()
          | Dh_vsome {dhd_key=s_k2; dhd_h=s_h2; evicted_to_blum = s_b2} ->
            let Record.Desc i_k2 i_h2 i_b2 = i_dh' in
            related_key_inj s_k s_k2 i_k i_k2;
            points_to_some_slot_related tsm st s_s' s_d i_d;
            if s_k2 <> s_k then ()
            else if
                 Some? s_r.TSM.record_parent_slot &&
                 (fst (Some?.v s_r.TSM.record_parent_slot) <> s_s' ||
                  snd (Some?.v s_r.TSM.record_parent_slot) <> s_d)
            then ()
            else if None? s_r.TSM.record_parent_slot
                 && S.points_to_some_slot tsm s_s' s_d
            then ()
            else (
              related_update_merkle_value
                s_mv' s_d s_k s_h
                i_mv' i_d i_k i_h false
            )
        )
      | _ -> ()

////////////////////////////////////////////////////////////////////////////////
// vevictb
////////////////////////////////////////////////////////////////////////////////

let related_sat_evictb_checks (#vcfg: _)
                              (tsm:TSM.thread_state_model)
                              (vtls:I.vtls vcfg)
                              (s_s:TSM.slot tsm.TSM.model_store_len)
                              (s_t:S_Types.timestamp)
                              (i_s:VCfg.slot_id vcfg)
                              (i_t:MSH.timestamp)
  : Lemma
    (requires
      I.Valid? vtls /\
      related_states tsm vtls /\
      related_slots s_s i_s /\
      related_clocks s_t i_t)
    (ensures
      S.sat_evictb_checks tsm s_s s_t ==
      I.sat_evictb_checks i_s i_t vtls)
    [SMTPat (S.sat_evictb_checks tsm s_s s_t);
     SMTPat (I.sat_evictb_checks i_s i_t vtls)]
  = let st = I.thread_store vtls in
    if IStore.inuse_slot (I.thread_store vtls) i_s
    then (
      points_to_some_slot_related tsm st s_s true BinTree.Left;
      points_to_some_slot_related tsm st s_s false BinTree.Right
    )

let related_vevictb (#vcfg: _)
                    (tsm:TSM.thread_state_model)
                    (vtls:I.vtls vcfg)
                    (v:S_Types.vlog_entry)
  : Lemma
    (requires
      S_Types.Ve_EvictB? v == true /\
      Some? (lift_log_entry #vcfg v) == true /\
      related_states tsm vtls /\
      I.Valid? vtls == true)
    (ensures (
      let open S_Types in
      let open IL in
      let { veeb_s = s_s; veeb_t = s_t} = Ve_EvictB?._0 v in
      let Some (EvictB_S i_s i_t) = lift_log_entry #vcfg v in
      S.vevictb_model tsm s_s s_t
        `related_states`
      I.vevictb i_s i_t vtls))
  = ()

////////////////////////////////////////////////////////////////////////////////
//vevictbm
////////////////////////////////////////////////////////////////////////////////

let related_vevictbm (#vcfg: _)
                     (tsm:TSM.thread_state_model)
                     (vtls:I.vtls vcfg)
                     (v:S_Types.vlog_entry)
  : Lemma
    (requires
      S_Types.Ve_EvictBM? v == true /\
      Some? (lift_log_entry #vcfg v) == true /\
      related_states tsm vtls /\
      I.Valid? vtls == true)
    (ensures (
      let open S_Types in
      let open IL in
      let { veebm_s = s_s; veebm_s2 = s_s'; veebm_t = s_t} = Ve_EvictBM?._0 v in
      let Some (EvictBM_S i_s i_s' i_t) = lift_log_entry #vcfg v in
      S.vevictbm_model tsm s_s s_s' s_t
        `related_states`
      I.vevictbm i_s i_s' i_t vtls))
  = ()

////////////////////

let related_entries (vcfg:_)
  (tsm:TSM.thread_state_model)
  (vtls:I.vtls vcfg)
  (s:Seq.seq (S_Types.vlog_entry))
  : Lemma
      (requires
        Some? (TSM.lift_log_entries #vcfg s) /\
        tsm `related_states` vtls)
      (ensures
        S.verify_model tsm s
          `related_states`
        I.verify vtls (Some?.v (TSM.lift_log_entries #vcfg s)))
      [SMTPat (tsm `related_states` vtls); SMTPat (S.verify_model tsm s)]
  = admit ()
