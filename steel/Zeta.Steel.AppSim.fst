module Zeta.Steel.AppSim

open Zeta.Steel.ThreadStateModel
open Zeta.Steel.Rel
open Zeta.Steel.LogRel
open Zeta.Steel.StoreRel
open Zeta.Steel.ThreadRelDef
open Zeta.Steel.AddMRel
open FStar.Classical

module M = Zeta.Merkle
module R = Zeta.Record
module KU = Zeta.Steel.KeyUtils
module TSM = Zeta.Steel.ThreadStateModel
module GK = Zeta.GenKey
module IS = Zeta.Intermediate.Store

module A = Zeta.App
module AT = Zeta.Steel.ApplicationTypes
module T = Zeta.Steel.FormatsManual
module U16 = FStar.UInt16
module GV = Zeta.GenericVerifier
module IV = Zeta.Intermediate.Verifier

#push-options "--fuel 1 --ifuel 1 --query_stats"

let related_slots (slots: Seq.seq s_slot_id) (i_slots: Seq.seq i_slot_id)
  = let open FStar.Seq in
    length slots = length i_slots /\
    (forall i. related_slot (index slots i) (index i_slots i))

(* read_slots succeeds on the list of slots; essentially each slot is occupied and contains an app record *)
let valid_app_slots (tsm: s_thread_state) (slots: Seq.seq s_slot_id)
  = Some? (read_slots tsm slots)

let rec valid_app_slots_implies_app_recs (tsm: s_thread_state) (slots: Seq.seq s_slot_id)
  : Lemma (requires (valid_app_slots tsm slots))
          (ensures (let st = tsm.store in
                    forall i. (let s = Seq.index slots i in
                           U16.v s < U16.v AT.store_size /\
                           inuse_slot st s /\
                           T.ApplicationKey? (stored_key st s))))
          (decreases (Seq.length slots))
          [SMTPat (valid_app_slots tsm slots)]
  = let n = Seq.length slots in
    let st = tsm.store in
    if n = 0 then ()
    else
    begin
      let hd = Seq.head slots in
      let tl = Seq.tail slots in
      assert (U16.v hd < U16.v AT.store_size);
      assert (inuse_slot st hd);
      assert (T.ApplicationKey? (stored_key st hd));

      assert (valid_app_slots tsm tl);
      valid_app_slots_implies_app_recs tsm tl;

      let aux (i:_)
        : Lemma (ensures (let s = Seq.index slots i in
                          U16.v s < U16.v AT.store_size /\
                          inuse_slot st s /\
                          T.ApplicationKey? (stored_key st s)))
        = if i > 0 then
            assert (Seq.index slots i = Seq.index tl (i-1))
      in
      forall_intro aux
    end

module SA = Zeta.SeqAux

let valid_app_slots_prop (tsm: s_thread_state) (slots: Seq.seq s_slot_id) (i: SA.seq_index slots)
  : Lemma (requires (valid_app_slots tsm slots))
          (ensures (let s = Seq.index slots i in
                    let st = tsm.store in
                    U16.v s < U16.v AT.store_size /\
                    inuse_slot st s /\
                    T.ApplicationKey? (stored_key st s)))
  = let s = Seq.index slots i in
    let st = tsm.store in
    valid_app_slots_implies_app_recs tsm slots;
    eliminate forall i. (let s = Seq.index slots i in
                           U16.v s < U16.v AT.store_size /\
                           inuse_slot st s /\
                           T.ApplicationKey? (stored_key st s))
    with i

#pop-options

#push-options "--z3rlimit_factor 3"

(* the key of the i'th record returned by read_slots is the key stored in i'th slot *)
let rec read_slots_key_idx (tsm: s_thread_state) (slots: Seq.seq s_slot_id) (i: SA.seq_index slots)
  : Lemma (requires (not tsm.failed /\ valid_app_slots tsm slots))
          (ensures (let s = Seq.index slots i in
                    let Some recs = read_slots tsm slots in
                    let keys = SA.map fst recs in
                    let ak1,_ = Seq.index recs i in
                    let st = tsm.store in
                    let T.ApplicationKey ak2 = stored_key st s in
                    ak1 = ak2 /\
                    ak1 = Seq.index keys i))
          (decreases (Seq.length slots))
  = let n = Seq.length slots in
    if n > 0 && i > 0 then
      read_slots_key_idx tsm (Seq.tail slots) (i-1)

let rec read_slots_val_idx (tsm: s_thread_state) (slots: Seq.seq s_slot_id) (i: SA.seq_index slots)
  : Lemma (requires (not tsm.failed /\ valid_app_slots tsm slots))
          (ensures (let s = Seq.index slots i in
                    let Some recs = read_slots tsm slots in
                    let _,av1 = Seq.index recs i in
                    let v = stored_value tsm.store s in
                    match v with
                    | T.MValue _ -> False
                    | T.DValue v -> match v with
                                 | None -> av1 = A.Null
                                 | Some v -> av1 = A.DValue v))
          (decreases (Seq.length slots))
  = let n = Seq.length slots in
    if n > 0 && i > 0 then
      read_slots_val_idx tsm (Seq.tail slots) (i-1)

#pop-options

let write_slots_precond (tsm: s_thread_state) (slots: Seq.seq s_slot_id)
  = forall (s:U16.t). Seq.contains slots s ==>
                 has_slot tsm s /\
                 T.ApplicationKey? (key_of_slot tsm s)

let rec write_slots_prop (tsm: s_thread_state)
                         (slots: Seq.seq s_slot_id {write_slots_precond tsm slots})
                         (values: Seq.seq (A.app_value_nullable app.A.adm) {Seq.length slots = Seq.length values})
  : Lemma (ensures (let tsm_ = write_slots tsm slots values in
                    identical_except_store tsm tsm_))
          (decreases (Seq.length slots))
          [SMTPat (write_slots tsm slots values)]
  = let n = Seq.length slots in
    if n > 0 then
    begin
      let hd_slot = Seq.head slots in
      let tl = Seq.tail slots in
      assert (slots `Seq.equal` Seq.cons hd_slot tl);
      Classical.forall_intro (Seq.contains_cons hd_slot tl);
      let hd_value =
        match Seq.head values with
        | A.Null -> T.DValue None
        | A.DValue d -> T.DValue (Some d)
      in
      let tsm2 = update_value tsm hd_slot hd_value in
      lemma_update_value tsm hd_slot hd_value;
      assert (identical_except_store tsm tsm2);
      write_slots_prop tsm2 (Seq.tail slots) (Seq.tail values);
      ()
    end

#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 3 --query_stats"

(* convert an nullable app value to its steel representation *)
let to_s_value (av: A.app_value_nullable app.A.adm)
  = match av with
    | A.Null -> T.DValue None
    | A.DValue d -> T.DValue (Some d)

let lemma_mem_head (slots: Seq.seq s_slot_id) (s: s_slot_id)
  : Lemma (requires (SA.distinct_elems slots /\ Seq.mem s slots /\ Seq.index_mem s slots = 0))
          (ensures (not (Seq.mem s (Seq.tail slots))))
  = let open FStar.Seq in
    let open SA in
    let tl = tail slots in
    if mem s tl then
    begin
      let i = index_mem s tl in
      assert (index tl i = s);
      assert (index slots (i+1) = s);
      lemma_elem_idx_uniq slots (i+1);
      assert (index_mem s slots = i+1); // contradiction
      ()
    end

let rec write_slots_slot_prop (tsm: s_thread_state)
                         (slots: Seq.seq s_slot_id {write_slots_precond tsm slots})
                         (values: Seq.seq (A.app_value_nullable app.A.adm) {Seq.length slots = Seq.length values})
                         (s: T.slot)
  : Lemma (requires (SA.distinct_elems slots))
          (ensures (let tsm_ = write_slots tsm slots values in
                    let st = tsm.store in
                    let st_ = tsm_.store in
                    let open TSM in
                    if Seq.mem s slots then
                      inuse_slot st s /\
                      inuse_slot st_ s /\
                      stored_key st s = stored_key st_ s /\
                      stored_value st_ s = to_s_value (Seq.index values (Seq.index_mem s slots)) /\
                      add_method_of st s = add_method_of st_ s /\
                      points_to_info st s true = points_to_info st_ s true /\
                      points_to_info st s false = points_to_info st_ s false /\
                      parent_info st s = parent_info st_ s
                    else get_slot st s == get_slot st_ s))
          (decreases (Seq.length slots))
  = let n = Seq.length slots in
    let st = tsm.store in
    let tsm_ = write_slots tsm slots values in
    let st_ = tsm_.store in
    if n > 0 then
    begin
      let hd_slot = Seq.head slots in
      let tl = Seq.tail slots in
      assert (slots `Seq.equal` Seq.cons hd_slot tl);
      Classical.forall_intro (Seq.contains_cons hd_slot tl);
      let hd_value =
        match Seq.head values with
        | A.Null -> T.DValue None
        | A.DValue d -> T.DValue (Some d)
      in
      assert (hd_value = to_s_value (Seq.head values));
      let tsm2 = update_value tsm hd_slot hd_value in
      lemma_update_value tsm hd_slot hd_value;
      write_slots_slot_prop tsm2 tl (Seq.tail values) s;
      if Seq.mem s slots then
      begin
        let i = Seq.index_mem s slots in
        if i = 0 then
        begin
          let st2 = tsm2.store in
          assert (hd_slot = s);
          assert (inuse_slot st2 s);
          assert (stored_key st2 s = stored_key st s);
          lemma_mem_head slots s;
          assert (stored_key st s = stored_key st_ s);
          assert (stored_value st_ s = to_s_value (Seq.index values i));
          ()
        end
        else
        begin
          assert (hd_slot <> s);
          let st2 = tsm2.store in
          assert (get_slot st2 s == get_slot st s);
          assert (Seq.mem s tl);
          ()
        end
      end
      else
      begin
        assert (s <> hd_slot);
        assert (not (Seq.mem s tl));
        ()
      end
    end

#pop-options

#push-options "--fuel 1 --ifuel 1 --query_stats"

let i_vspec = IV.int_verifier_spec i_vcfg

let i_contains_only_app_keys (tsm: s_thread_state) (slots: Seq.seq s_slot_id)
                    (i_tsm: i_thread_state) (i_slots: Seq.seq i_slot_id)
  : Lemma (requires (related_tsm tsm i_tsm /\ related_slots slots i_slots /\
                     not tsm.failed /\ valid_app_slots tsm slots /\
                     check_distinct_keys (Some?.v (read_slots tsm slots))))
          (ensures (GV.contains_only_app_keys #i_vspec i_tsm i_slots))
  = let i_st = i_tsm.IV.st in
    let st = tsm.store in
    assert (related_store st i_st);

    let aux (i:_)
      : Lemma (ensures (GV.contains_app_key #i_vspec i_tsm (Seq.index i_slots i)))
      = let i_s = Seq.index i_slots i in
        let s = Seq.index slots i in
        eliminate forall i. related_slot (Seq.index slots i) (Seq.index i_slots i)
        with i;
        assert (related_slot s i_s);
        eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
        with i_s;
        eliminate forall i. (let s = Seq.index slots i in
                           U16.v s < U16.v AT.store_size /\
                           inuse_slot st s /\
                           T.ApplicationKey? (stored_key st s))
        with i
    in
    forall_intro aux

let related_app_keys
  (tsm: s_thread_state) (slots: Seq.seq s_slot_id)
  (i_tsm: i_thread_state) (i_slots: Seq.seq i_slot_id)
  (i: SA.seq_index slots)
  : Lemma (requires (related_tsm tsm i_tsm /\ related_slots slots i_slots /\ not tsm.failed /\
                     valid_app_slots tsm slots))
          (ensures (let Some recs = read_slots tsm slots in
                    let ak,_ = Seq.index recs i in
                    let i_s = Seq.index i_slots i in
                    let i_ak = GV.to_app_key #i_vspec i_tsm i_s in
                    ak = i_ak))
  = let Some recs = read_slots tsm slots in
    let ak,_ = Seq.index recs i in

    let st = tsm.store in
    let s = Seq.index slots i in
    let i_s = Seq.index i_slots i in
    let i_st = i_tsm.IV.st in

    eliminate forall i. related_slot (Seq.index slots i) (Seq.index i_slots i)
    with i;
    assert (related_slot s i_s);

    assert (related_store st i_st);

    // slot entries s/i_s within the stores are related
    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s;

    let gk = stored_key st s in
    let i_gk = IS.stored_key i_st i_s in
    assert (related_key gk i_gk);

    read_slots_key_idx tsm slots i;
    related_app_key gk i_gk;
    ()

let i_contains_distinct_app_keys (tsm: s_thread_state) (slots: Seq.seq s_slot_id)
                    (i_tsm: i_thread_state) (i_slots: Seq.seq i_slot_id)
  : Lemma (requires (related_tsm tsm i_tsm /\ related_slots slots i_slots /\
                     not tsm.failed /\ valid_app_slots tsm slots /\
                     check_distinct_keys (Some?.v (read_slots tsm slots))))
          (ensures (GV.contains_distinct_app_keys #i_vspec i_tsm i_slots))
  = i_contains_only_app_keys tsm slots i_tsm i_slots;
    let Some recs = read_slots tsm slots in
    let aux (i1 i2:_)
      : Lemma (ensures (i1 <> i2 ==> GV.to_app_key #i_vspec i_tsm (Seq.index i_slots i1) <>
                                    GV.to_app_key #i_vspec i_tsm (Seq.index i_slots i2)))
      = if i1 <> i2 then
        begin
          let i_s1 = Seq.index i_slots i1 in
          let s1 = Seq.index slots i1 in
          let i_s2 = Seq.index i_slots i2 in
          let s2 = Seq.index slots i2 in
          eliminate forall i. related_slot (Seq.index slots i) (Seq.index i_slots i)
          with i1;
          eliminate forall i. related_slot (Seq.index slots i) (Seq.index i_slots i)
          with i2;

          related_app_keys tsm slots i_tsm i_slots i1;
          related_app_keys tsm slots i_tsm i_slots i2;
          let ak1,_ = Seq.index recs i1 in
          let ak2,_ = Seq.index recs i2 in
          assert (ak1 <> ak2);

          ()
        end
    in
    forall_intro_2 aux

let reads_identical_idx (tsm: s_thread_state) (slots: Seq.seq s_slot_id)
                    (i_tsm: i_thread_state) (i_slots: Seq.seq i_slot_id)
                    (i: SA.seq_index slots)
  : Lemma (requires (related_tsm tsm i_tsm /\ related_slots slots i_slots /\
                     not tsm.failed /\ valid_app_slots tsm slots /\
                     check_distinct_keys (Some?.v (read_slots tsm slots))))
          (ensures (GV.contains_distinct_app_keys #i_vspec i_tsm i_slots /\
                    (let Some rds = read_slots tsm slots in
                     let i_rds = GV.reads #i_vspec i_tsm i_slots in
                     Seq.index rds i = Seq.index i_rds i)))
  = i_contains_distinct_app_keys tsm slots i_tsm i_slots;
    let Some rds = read_slots tsm slots in
    let i_rds = GV.reads #i_vspec i_tsm i_slots in
    read_slots_val_idx tsm slots i;

    eliminate forall i. related_slot (Seq.index slots i) (Seq.index i_slots i)
    with i;

    let s = Seq.index slots i in
    let i_s = Seq.index i_slots i in
    assert (related_slot s i_s);

    let st = tsm.store in
    let i_st = i_tsm.IV.st in

    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s;

    let v = stored_value st s in
    let i_v = IS.stored_value i_st i_s in
    assert (related_val v i_v);

    let T.DValue av = v in
    let R.AppV i_av = i_v in
    assert (related_dval av i_av);

    related_app_keys tsm slots i_tsm i_slots i

let reads_identical (tsm: s_thread_state) (slots: Seq.seq s_slot_id)
                    (i_tsm: i_thread_state) (i_slots: Seq.seq i_slot_id)
  : Lemma (requires (related_tsm tsm i_tsm /\ related_slots slots i_slots /\
                     not tsm.failed /\ valid_app_slots tsm slots /\
                     check_distinct_keys (Some?.v (read_slots tsm slots))))
          (ensures (GV.contains_distinct_app_keys #i_vspec i_tsm i_slots /\
                    Some?.v (read_slots tsm slots) == GV.reads #i_vspec i_tsm i_slots))
  = i_contains_distinct_app_keys tsm slots i_tsm i_slots;
    let Some rds = read_slots tsm slots in
    let i_rds = GV.reads #i_vspec i_tsm i_slots in
    assert (Seq.length rds = Seq.length i_rds);
    let aux (i:_)
      : Lemma (ensures (Seq.index rds i == Seq.index i_rds i))
      = reads_identical_idx tsm slots i_tsm i_slots i
    in
    forall_intro aux;
    assert (Seq.equal rds i_rds);
    ()

let related_slots_mem (slots: Seq.seq s_slot_id) (i_slots: Seq.seq i_slot_id)
                      (s: s_slot_id) (i_s: i_slot_id)
  : Lemma (requires (related_slots slots i_slots /\ related_slot s i_s /\ SA.distinct_elems slots))
          (ensures (Seq.mem s slots = Seq.mem i_s i_slots /\
                    (Seq.mem s slots ==> Seq.index_mem s slots = Seq.index_mem i_s i_slots)))
  = let open FStar.Seq in
    if mem s slots then
    begin
      let j = index_mem s slots in
      eliminate forall i. related_slot (index slots i) (index i_slots i)
      with j;
      let i_s' = index i_slots j in
      assert (related_slot s i_s');
      assert (i_s = i_s');
      assert (mem i_s i_slots);

      let j' = index_mem i_s i_slots in
      if j' <> j then
      begin

        eliminate forall i. related_slot (index slots i) (index i_slots i)
        with j';

        let s' = index slots j' in
        assert (s' = s);

        SA.lemma_elem_idx_uniq slots j';
        assert (index_mem s slots = j');
        ()
      end
    end
    else if mem i_s i_slots then
    begin
      let j = index_mem i_s i_slots in
      eliminate forall i. related_slot (index slots i) (index i_slots i)
      with j;
      let s' = index slots j in
      assert (related_slot s' i_s);
      assert (s' = s);
      ()
    end

let related_writes (tsm: s_thread_state) (slots: Seq.seq s_slot_id)
                   (i_tsm: i_thread_state) (i_slots: Seq.seq i_slot_id)
                   (values: Seq.seq (A.app_value_nullable app.A.adm) {Seq.length slots = Seq.length values})
  : Lemma (requires (related_tsm tsm i_tsm /\ related_slots slots i_slots /\ not tsm.failed /\
                     SA.distinct_elems slots /\
                     IS.contains_only_app_keys i_tsm.IV.st i_slots /\
                      ( forall (s:U16.t). Seq.contains slots s ==>
                                     has_slot tsm s /\
                                     T.ApplicationKey? (key_of_slot tsm s))))
          (ensures (let tsm_ = write_slots tsm slots values in
                    let i_tsm_ = i_vspec.GV.puts i_tsm i_slots values in
                    related_tsm tsm_ i_tsm_))
  = let st = tsm.store in
    let tsm_ = write_slots tsm slots values in
    let st_ = tsm_.store in
    let i_st = i_tsm.IV.st in
    let i_tsm_ = i_vspec.GV.puts i_tsm i_slots values in
    let i_st_ = i_tsm_.IV.st in

    let aux (i_s:_)
      : Lemma (ensures (related_store_entry_opt (Seq.index st_ i_s) (Seq.index i_st_ i_s)))
      = let s: T.slot = U16.uint_to_t i_s in

        write_slots_slot_prop tsm slots values s;
        related_slots_mem slots i_slots s i_s;
        assert (related_store st i_st);

        eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
        with i_s;

        if Seq.mem s slots then
        begin
          IS.puts_preserves i_st i_slots values i_s;
          IS.puts_ref_value i_st i_slots values i_s
        end
        else
          IS.puts_preserves_non_ref i_st i_slots values i_s
    in
    forall_intro aux;
    ()

let runapp_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     T.RunApp? se /\ not tsm.failed))
          (ensures (let T.RunApp p = se in
                    let tsm_ = runapp tsm p in
                    let i_tsm_ = GV.verify_step ie i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))
  = let T.RunApp p = se in
    let tsm_ = runapp tsm p in

    let GV.RunApp i_fid i_arg i_slots = ie in

    let st = tsm.store in
    let i_st = i_tsm.IV.st in
    assert (related_store st i_st);

    if not tsm_.failed then
    begin
      assert (Map.contains app.A.tbl p.fid);
      assert (p.fid = i_fid);   // related_log_entry

      match AT.spec_app_parser p.fid p.rest.ebytes with
      | Some ((arg, slots), len) ->
        assert (arg = i_arg);
        assert (related_slots slots i_slots);

        // all slots are distinct
        assert (Zeta.SeqAux.distinct_elems slots);

        let fsig = Map.sel app.A.tbl p.fid in
        let fn = A.appfn i_fid in

        match read_slots tsm slots with
        | Some recs ->
          assert (check_distinct_keys recs);
          reads_identical tsm slots i_tsm i_slots;

          let i_rs = GV.reads i_tsm i_slots in
          assert (i_rs == recs);

          let res = fsig.f arg recs in
          let i_rc, _, i_ws = fn i_arg i_rs in

          match res with
          | (_, res, out_vals) ->
            assert (i_rc <> A.Fn_failure);
            assert (i_ws == out_vals);
            let tsm2 = {tsm with app_results=Seq.Properties.snoc tsm.app_results (| p.fid, arg, recs, res |)} in
            assert (related_tsm tsm2 i_tsm);
            assert (GV.contains_only_app_keys i_tsm i_slots);
            assert (IS.contains_only_app_keys i_st i_slots);
            related_writes tsm2 slots i_tsm i_slots out_vals
    end

#pop-options

#push-options "--fuel 1 --ifuel 1 --query_stats"

let runapp_output (tsm: s_thread_state)
                  (se: s_log_entry {valid_runapp_param tsm se})
  : GTot (o:runapp_out_t {let T.RunApp p = se in
                          let tsm_ = runapp tsm p in
                          tsm_.app_results = Seq.snoc tsm.app_results o})
  = let T.RunApp p = se in
    let tsm_ = runapp tsm p in

    match AT.spec_app_parser p.fid p.rest.ebytes with
    | Some ((arg, slots), _ ) ->
      let fsig = Map.sel app.A.tbl p.fid in

      match read_slots tsm slots with
      | Some recs ->

        let res = fsig.f arg recs in
        match res with
        | (_, res, out_vals) ->
          let o = (| p.fid, arg, recs, res |) in
          let tsm2 = {tsm with app_results=Seq.Properties.snoc tsm.app_results o} in
          assert (tsm_ == write_slots tsm2 slots out_vals);
          write_slots_prop tsm2 slots out_vals;
          o

#pop-options

#push-options "--ifuel 1 --fuel 2 --query_stats"

let runapp_output_related (tsm: s_thread_state)
                          (i_tsm: i_thread_state)
                          (se: s_log_entry)
                          (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     not tsm.failed /\
                     valid_runapp_param tsm se))
          (ensures (let res = runapp_output tsm se in
                    let i_tsm_ = GV.verify_step ie i_tsm in
                    GV.is_appfn ie /\
                    i_tsm_.IV.valid /\
                    (let i_res = GV.appfn_result ie i_tsm in
                     related_output res i_res)))
  = runapp_simulation tsm i_tsm se ie;

    let res = runapp_output tsm se in
    let i_tsm_ = GV.verify_step ie i_tsm in

    assert (GV.is_appfn ie);

    let T.RunApp p = se in
    let GV.RunApp i_fid i_arg i_slots = ie in

    let st = tsm.store in
    let i_st = i_tsm.IV.st in
    assert (related_store st i_st);

    assert (p.fid = i_fid);

    match AT.spec_app_parser p.fid p.rest.ebytes with
    | Some ((arg, slots), len) ->
      assert (arg = i_arg);
      assert (related_slots slots i_slots);

      // all slots are distinct
      assert (Zeta.SeqAux.distinct_elems slots);

      let fsig = Map.sel app.A.tbl p.fid in
      let fn = A.appfn i_fid in

      match read_slots tsm slots with
      | Some recs ->
        assert (check_distinct_keys recs);
        reads_identical tsm slots i_tsm i_slots;

        let i_rs = GV.reads i_tsm i_slots in
        assert (i_rs == recs);

        let _, o, _ = fsig.f arg recs in
        let i_rc, i_o, i_ws = fn i_arg i_rs in

        let i_res: AS.appfn_call_res app = { AS.fid_cr = i_fid;
                                             AS.arg_cr = i_arg;
                                             AS.inp_cr = i_rs;
                                             AS.res_cr = i_o } in

        assert (i_res == GV.appfn_result ie i_tsm);
        ()

#pop-options
