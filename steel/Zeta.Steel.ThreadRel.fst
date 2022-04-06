module Zeta.Steel.ThreadRel

open FStar.Classical
open Zeta.Steel.ThreadSim
open Zeta.Steel.AppSim

module A = Zeta.App
module M = Zeta.Merkle
module R = Zeta.Record
module T = Zeta.Steel.FormatsManual
module S = FStar.Seq
module SA = Zeta.SeqAux
module KU = Zeta.Steel.KeyUtils
module GK = Zeta.GenKey
module IS = Zeta.Intermediate.Store
module SS = Zeta.Steel.StoreRel
module HA = Zeta.Steel.HashAccumulator
module LT = Zeta.Steel.LogEntry.Types

#push-options "--fuel 1 --ifuel 2 --query_stats"

let addm_processed_entries_props (tsm: thread_state_model) (e: s_log_entry {T.AddM? e})
  : Lemma (ensures (let open T in
                    let LT.AddM s s' r = e in
                    let tsm_ = vaddm tsm s s' r in
                    tsm_.processed_entries == tsm.processed_entries))
  = ()

let addm_thread_id_prop (tsm: thread_state_model) (e: s_log_entry {T.AddM? e})
  : Lemma (ensures (let open T in
                    let AddM s s' r = e in
                    let tsm_ = vaddm tsm s s' r in
                    tsm_.thread_id == tsm.thread_id))
  = ()

let addm_valid_log_entry_prop (tsm: thread_state_model) (e: s_log_entry {T.AddM? e})
  : Lemma (ensures (let open T in
                    let AddM s s' r = e in
                    let tsm_ = vaddm tsm s s' r in
                    not tsm_.failed ==> valid_log_entry e))
  = ()

#pop-options

let runapp_slots_prop (tsm: thread_state_model) (slots: S.seq T.slot_id)
  = forall (s:U16.t). Seq.contains slots s ==>
                  has_slot tsm s /\
                  T.ApplicationKey? (key_of_slot tsm s)

let rec read_slots_valid_prop (tsm: thread_state_model) (slots: S.seq T.slot_id)
  : Lemma (ensures (let or = read_slots tsm slots in
                    Some? or ==> (forall i. valid_slot (S.index slots i))))
          (decreases (S.length slots))
  = let or = read_slots tsm slots in
    if Some? or && S.length slots > 0 then (
      let hd = S.head slots in
      let tl = S.tail slots in
      Classical.forall_intro (Seq.contains_cons hd tl);

      read_slots_valid_prop tsm tl;
      assert(valid_slot hd);
      let aux (i:_)
        : Lemma (ensures (valid_slot (S.index slots i)))
        = if i > 0 then
            assert(valid_slot (S.index tl (i-1)))
      in
      forall_intro aux
    )

let rec write_slots_non_store_prop
  (tsm: thread_state_model)
  (slots: _ {runapp_slots_prop tsm slots})
  (values: S.seq (app_value_nullable app.adm) {S.length slots == S.length values})
  : Lemma (ensures (let tsm_ = write_slots tsm slots values in
                    tsm_.failed == tsm.failed /\
                    tsm_.clock == tsm.clock /\
                    tsm_.epoch_hashes == tsm.epoch_hashes /\
                    tsm_.thread_id == tsm.thread_id /\
                    tsm_.processed_entries == tsm.processed_entries /\
                    tsm_.app_results == tsm.app_results))
          (decreases (S.length slots))
  = let tsm_ = write_slots tsm slots values in
    if S.length slots > 0 then (
      let hd_slot = S.head slots in
      let tl = S.tail slots in
      assert(slots `S.equal` S.cons hd_slot tl);
      Classical.forall_intro (Seq.contains_cons hd_slot tl);
      let hd_value =
        match Seq.head values with
        | Null -> T.DValue None
        | DValue d -> T.DValue (Some d)
      in
      let tsm = update_value tsm hd_slot hd_value in
      write_slots_non_store_prop tsm (S.tail slots) (S.tail values)
    )

(* do all the runapp_checks satisfy *)
let runapp_checks_sat (tsm: thread_state_model) (pl: T.runApp_payload)
  : GTot bool
  = let open T in
    if not (Map.contains app.tbl pl.fid)
    then false //unknown fid
    else (
      match AT.spec_app_parser pl.fid pl.rest.ebytes with
      | None -> false //parsing failed
      | Some ((arg, slots), len) ->
        if len <> U32.v pl.rest.len
        then false //parsing failed, some bytes not consumed
        else if not (Zeta.SeqAux.distinct_elems_comp slots)
        then false //not distinct slots
        else
          let fsig = Map.sel app.tbl pl.fid in
          match read_slots tsm slots with
          | None -> false
          | Some recs ->
            if not (check_distinct_keys recs)
            then false
            else (
              let res = fsig.f arg recs in
              match res with
              | ( Fn_failure, _, _) -> false
              | (_, res, out_vals) -> true
            )
        )

let runapp_checks_unsat_prop (tsm: thread_state_model) (pl: T.runApp_payload)
  : Lemma (ensures (not (runapp_checks_sat tsm pl) ==> fail tsm == runapp tsm pl))
  = ()

let runapp_non_store_prop (tsm: thread_state_model) (e: s_log_entry {T.RunApp? e})
  : Lemma (ensures (let open T in
                    let RunApp p = e in
                    let tsm_ = runapp tsm p in
                    tsm_.processed_entries == tsm.processed_entries /\
                    tsm_.thread_id = tsm.thread_id))
  = let open T in
    let RunApp p = e in
    let tsm_ = runapp tsm p in
    runapp_checks_unsat_prop tsm p;
    if runapp_checks_sat tsm p then
      match AT.spec_app_parser p.fid p.rest.ebytes with
      | Some ((arg, slots), len) ->
        let fsig = Map.sel app.tbl p.fid in
        match read_slots tsm slots with
        | Some recs ->
          let res = fsig.f arg recs in
          match res with
          | _, res, out_vals ->
            let tsm = {tsm with app_results=Seq.Properties.snoc tsm.app_results (| p.fid, arg, recs, res |)} in
            write_slots_non_store_prop tsm slots out_vals

let runapp_valid_log_entry_prop (tsm: thread_state_model) (e: s_log_entry {T.RunApp? e})
  : Lemma (ensures (let open T in
                    let RunApp p = e in
                    let tsm_ = runapp tsm p in
                    not tsm_.failed ==> valid_log_entry e))
  = let open T in
    let RunApp p = e in
    let tsm_ = runapp tsm p in
    runapp_checks_unsat_prop tsm p;
    if runapp_checks_sat tsm p && not tsm_.failed then
      match AT.spec_app_parser p.fid p.rest.ebytes with
      | Some ((arg, slots), len) ->
        read_slots_valid_prop tsm slots

let verify_step_model_processed_entries_prop (tsm: thread_state_model) (e: s_log_entry)
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    not tsm_.failed ==> tsm_.processed_entries == Seq.snoc tsm.processed_entries e))
          [SMTPat (verify_step_model tsm e)]
  = let open T in
    if not tsm.failed then
      match e with
      | AddM _ _ _ -> addm_processed_entries_props tsm e
      | RunApp _ -> runapp_non_store_prop tsm e
      | _ -> ()

let verify_step_model_thread_id_prop (tsm: thread_state_model) (e: s_log_entry)
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    tsm_.thread_id = tsm.thread_id))
          [SMTPat (verify_step_model tsm e)]
  = let open T in
    match e with
    | AddM _ _ _ -> addm_thread_id_prop tsm e
    | RunApp _ -> runapp_non_store_prop tsm e
    | _ -> ()

let verify_step_model_valid_log_entry_prop (tsm: thread_state_model) (e: s_log_entry)
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    not tsm_.failed ==> valid_log_entry e))
          [SMTPat (verify_step_model tsm e)]
  = let open T in
    let tsm_ = verify_step_model tsm e in
    if not tsm_.failed then (
      match e with
      | AddM _ _ _ -> addm_valid_log_entry_prop tsm e
      | RunApp _ -> runapp_valid_log_entry_prop tsm e
      | _ -> ()
    )

let rec run_implies_processed_entries (tid: AT.tid) (l: s_log)
  : Lemma (ensures (let tsm = run tid l in
                    tsm.failed \/
                    tsm.processed_entries == l))
          (decreases (S.length l))
  = let tsm = run tid l in
    if S.length l = 0 then
      S.lemma_empty l
    else (
      let i = S.length l - 1 in
      let l' = SA.prefix l i in
      let e = S.index l i in
      run_implies_processed_entries tid l';
      let tsm' = run tid l' in

      if not tsm'.failed && not tsm.failed then (
        verify_step_model_processed_entries_prop tsm' e;
        SA.lemma_hprefix_append_telem l
      )
    )

let rec run_implies_thread_id (tid: AT.tid) (l: s_log)
  : Lemma (ensures (let tsm = run tid l in
                    tsm.thread_id = tid))
          (decreases (S.length l))
  = let tsm = run tid l in
    if S.length l > 0 then (
      let i = S.length l - 1 in
      let l' = SA.prefix l i in
      let e = S.index l i in
      run_implies_thread_id tid l';
      verify_step_model_thread_id_prop (run tid l') e;
      ()
    )

let run_implies_valid (tid: AT.tid) (l: s_log)
  : Lemma (ensures (let tsm = run tid l in
                    tsm.failed \/ valid tsm))
  = let tsm = run tid l in
    run_implies_processed_entries tid l;
    run_implies_thread_id tid l

let rec run_implies_valid_log (tid: AT.tid) (l: s_log)
  : Lemma (ensures (let tsm = run tid l in
                    not tsm.failed ==> valid_log l))
          (decreases (S.length l))
  = let tsm = run tid l in
    if S.length l > 0 then (
      let i = S.length l - 1 in
      let l' = SA.prefix l i in
      let e = S.index l i in
      let tsm' = run tid l' in
      run_implies_valid_log tid l';
      verify_step_model_valid_log_entry_prop (run tid l') e;
      if not tsm.failed then (
        assert(valid_log l');
        assert(valid_log_entry e);
        let aux (j:_)
          : Lemma (ensures (valid_log_entry (S.index l j)))
          = if j < i then
              eliminate forall i. valid_log_entry (S.index l' i) with j
        in
        forall_intro aux
      )
    )

let valid_implies_valid_log (tsm: valid_tsm)
  : Lemma (ensures (valid_log tsm.processed_entries))
  = run_implies_valid tsm.thread_id tsm.processed_entries;
    run_implies_valid_log tsm.thread_id tsm.processed_entries

let verify_step_model_extends_validity (tsm: valid_tsm) (e: s_log_entry)
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    not tsm_.failed ==> valid tsm_))
          [SMTPat (verify_step_model tsm e)]
  = let l = tsm.processed_entries in
    let t = tsm.thread_id in
    let l_ = SA.append1 l e in
    let tsm_ = run t l_ in
    SA.lemma_prefix1_append l e;
    assert(l == SA.prefix l_ (S.length l));
    run_implies_valid t l_

let to_i_tl (tsm: valid_tsm {spec_rel_base tsm})
  : GTot (Zeta.Intermediate.Thread.verifiable_log i_vcfg)
  = let i_log = lift_log tsm.processed_entries in
    let i_tid = lift_tid tsm.thread_id in
    i_tid, i_log

let to_i_tsm (tsm: valid_tsm {spec_rel_base tsm})
  : GTot (i_thread_state)
  = Zeta.Generic.Thread.state (to_i_tl tsm)

let verify_step_model_lifted_log_prop (tsm:_ {spec_rel_base tsm}) (e: s_log_entry)
  : Lemma (requires (let tsm_ = verify_step_model tsm e in
                     not tsm_.failed))
          (ensures (let tsm_ = verify_step_model tsm e in
                    let i_log = lift_log tsm.processed_entries in
                    let i_e = lift_log_entry e in
                    let i_log_ = lift_log tsm_.processed_entries in
                    let i = Seq.length i_log in
                    i_log_ == Seq.snoc i_log i_e /\
                    Seq.index i_log_ i = i_e /\
                    i_log = SA.prefix i_log_ i))
          [SMTPat (verify_step_model tsm e)]
  = let i_log = lift_log tsm.processed_entries in
    let i_e = lift_log_entry e in
    lift_log_snoc tsm.processed_entries e;
    SA.lemma_prefix1_append i_log i_e

let spec_rel_base_addm (tsm:_ {spec_rel_base tsm}) (e: s_log_entry {T.AddM? e})
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    not tsm_.failed ==> valid tsm_ /\ spec_rel_base tsm_))
  = let open T in
    let tid = tsm.TSM.thread_id in
    let i_tid = lift_tid tid in
    let tsm_ = verify_step_model tsm e in

    let i_log = lift_log tsm.processed_entries in
    let i_tsm = to_i_tsm tsm in

    if not tsm_.failed then (
      (* verify_step extends validity or fails *)
      assert(valid tsm_);

      let i_e = lift_log_entry e in
      assert (related_log_entry e i_e);

      let i_tsm_ = GV.verify_step i_e i_tsm in
      let i_log_ = lift_log tsm_.processed_entries in
      addm_simulation tsm i_tsm e i_e
    )

let spec_rel_base_addb (tsm:_ {spec_rel_base tsm}) (e: s_log_entry {T.AddB? e})
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    not tsm_.failed ==> valid tsm_ /\ spec_rel_base tsm_))
  = let open T in
    let tid = tsm.TSM.thread_id in
    let i_tid = lift_tid tid in
    let tsm_ = verify_step_model tsm e in

    let i_log = lift_log tsm.processed_entries in
    let i_tsm = to_i_tsm tsm in

    if not tsm_.failed then (
      (* verify_step extends validity or fails *)
      assert(valid tsm_);

      let i_e = lift_log_entry e in
      assert (related_log_entry e i_e);

      let i_tsm_ = GV.verify_step i_e i_tsm in
      let i_log_ = lift_log tsm_.processed_entries in
      addb_simulation tsm i_tsm e i_e
    )

let spec_rel_base_evictm (tsm:_ {spec_rel_base tsm}) (e: s_log_entry {T.EvictM? e})
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    not tsm_.failed ==> valid tsm_ /\ spec_rel_base tsm_))
  = let open T in
    let tid = tsm.TSM.thread_id in
    let i_tid = lift_tid tid in
    let tsm_ = verify_step_model tsm e in

    let i_log = lift_log tsm.processed_entries in
    let i_tsm = to_i_tsm tsm in

    if not tsm_.failed then (
      (* verify_step extends validity or fails *)
      assert(valid tsm_);

      let i_e = lift_log_entry e in
      assert (related_log_entry e i_e);

      let i_tsm_ = GV.verify_step i_e i_tsm in
      let i_log_ = lift_log tsm_.processed_entries in
      evictm_simulation tsm i_tsm e i_e
    )

let spec_rel_base_evictb (tsm:_ {spec_rel_base tsm}) (e: s_log_entry {T.EvictB? e})
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    not tsm_.failed ==> valid tsm_ /\ spec_rel_base tsm_))
  = let open T in
    let tid = tsm.TSM.thread_id in
    let i_tid = lift_tid tid in
    let tsm_ = verify_step_model tsm e in

    let i_log = lift_log tsm.processed_entries in
    let i_tsm = to_i_tsm tsm in

    if not tsm_.failed then (
      (* verify_step extends validity or fails *)
      assert(valid tsm_);

      let i_e = lift_log_entry e in
      assert (related_log_entry e i_e);

      let i_tsm_ = GV.verify_step i_e i_tsm in
      let i_log_ = lift_log tsm_.processed_entries in
      evictb_simulation tsm i_tsm e i_e
    )

let spec_rel_base_evictbm (tsm:_ {spec_rel_base tsm}) (e: s_log_entry {T.EvictBM? e})
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    not tsm_.failed ==> valid tsm_ /\ spec_rel_base tsm_))
  = let open T in
    let tid = tsm.TSM.thread_id in
    let i_tid = lift_tid tid in
    let tsm_ = verify_step_model tsm e in

    let i_log = lift_log tsm.processed_entries in
    let i_tsm = to_i_tsm tsm in

    if not tsm_.failed then (
      (* verify_step extends validity or fails *)
      assert(valid tsm_);

      let i_e = lift_log_entry e in
      assert (related_log_entry e i_e);

      let i_tsm_ = GV.verify_step i_e i_tsm in
      let i_log_ = lift_log tsm_.processed_entries in
      evictbm_simulation tsm i_tsm e i_e
    )

let spec_rel_base_nextepoch (tsm:_ {spec_rel_base tsm}) (e: s_log_entry {T.NextEpoch? e})
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    not tsm_.failed ==> valid tsm_ /\ spec_rel_base tsm_))
  = let open T in
    let tid = tsm.TSM.thread_id in
    let i_tid = lift_tid tid in
    let tsm_ = verify_step_model tsm e in

    let i_log = lift_log tsm.processed_entries in
    let i_tsm = to_i_tsm tsm in

    if not tsm_.failed then (
      (* verify_step extends validity or fails *)
      assert(valid tsm_);

      let i_e = lift_log_entry e in
      assert (related_log_entry e i_e);

      let i_tsm_ = GV.verify_step i_e i_tsm in
      let i_log_ = lift_log tsm_.processed_entries in
      nextepoch_simulation tsm i_tsm e i_e
    )

let spec_rel_base_verifyepoch (tsm:_ {spec_rel_base tsm}) (e: s_log_entry {T.VerifyEpoch? e})
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    not tsm_.failed ==> valid tsm_ /\ spec_rel_base tsm_))
  = let open T in
    let tid = tsm.TSM.thread_id in
    let i_tid = lift_tid tid in
    let tsm_ = verify_step_model tsm e in

    let i_log = lift_log tsm.processed_entries in
    let i_tsm = to_i_tsm tsm in

    if not tsm_.failed then (
      (* verify_step extends validity or fails *)
      assert(valid tsm_);

      let i_e = lift_log_entry e in
      assert (related_log_entry e i_e);

      let i_tsm_ = GV.verify_step i_e i_tsm in
      let i_log_ = lift_log tsm_.processed_entries in
      verifyepoch_simulation tsm i_tsm e i_e
    )

let spec_rel_base_runapp (tsm:_ {spec_rel_base tsm}) (e: s_log_entry {T.RunApp? e})
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    not tsm_.failed ==> valid tsm_ /\ spec_rel_base tsm_))
  = let open T in
    let tid = tsm.TSM.thread_id in
    let i_tid = lift_tid tid in
    let tsm_ = verify_step_model tsm e in

    let i_log = lift_log tsm.processed_entries in
    let i_tsm = to_i_tsm tsm in

    if not tsm_.failed then (
      (* verify_step extends validity or fails *)
      assert(valid tsm_);

      let i_e = lift_log_entry e in
      assert (related_log_entry e i_e);

      let i_tsm_ = GV.verify_step i_e i_tsm in
      let i_log_ = lift_log tsm_.processed_entries in
      runapp_simulation tsm i_tsm e i_e
    )

let lemma_verify_step_model_spec_rel_base (tsm:_ {spec_rel_base tsm}) (e: s_log_entry)
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    not tsm_.failed ==> valid tsm_ /\ spec_rel_base tsm_))
          [SMTPat (verify_step_model tsm e)]
  = let open T in
    match e with
    | AddM _ _ _ -> spec_rel_base_addm tsm e
    | AddB _ _ _ _ -> spec_rel_base_addb tsm e
    | EvictM _ -> spec_rel_base_evictm tsm e
    | EvictB _ -> spec_rel_base_evictb tsm e
    | EvictBM _ -> spec_rel_base_evictbm tsm e
    | NextEpoch -> spec_rel_base_nextepoch tsm e
    | VerifyEpoch -> spec_rel_base_verifyepoch tsm e
    | RunApp _ -> spec_rel_base_runapp tsm e

let init_tsm_valid (tid: AT.tid)
  : Lemma (ensures (valid (init_thread_state_model tid)))
          [SMTPat (init_thread_state_model tid)]
  = ()

let empty_store_related ()
  : Lemma (ensures (let st = Seq.create (U16.v AT.store_size) None in
                    let i_st = IS.empty_store i_vcfg in
                    related_store st i_st))
  = let st: contents = Seq.create (U16.v AT.store_size) None in
    let i_st = IS.empty_store i_vcfg in

    let aux (i:_)
      : Lemma (ensures (related_store_entry_opt (Seq.index st i) (Seq.index i_st i)))
      = ()
    in
    forall_intro aux

let related_madd_to_store_root (tsm: thread_state_model)
                               (i_st: i_store)
                               (s: T.slot) (i_s: i_slot_id)
                               (v: T.value) (i_v: i_val {Zeta.Record.IntV? i_v})
  : Lemma (requires (related_store tsm.store i_st /\ related_slot s i_s /\
                     IS.empty_slot i_st i_s /\
                     related_val v i_v))
          (ensures (let tsm_ = TSM.madd_to_store_root tsm s v in
                    let st_ = tsm_.store in
                    let i_st_ = IS.madd_to_store_root i_st i_s i_v in
                    related_store st_ i_st_))
  = let st = tsm.store in

    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s;

    assert (not (has_slot tsm s));
    assert (LT.is_value_of root_key v);

    let new_entry = {
      key = root_key;
      value = v;
      add_method = MAdd;
      l_child_in_store = None;
      r_child_in_store = None;
      parent_slot = None;
    } in

    let st_ = Seq.upd tsm.store (U16.v s) (Some new_entry) in
    let tsm_ = madd_to_store_root tsm s v in
    assert (tsm_.store == st_);

    let i_st_ = IS.madd_to_store_root i_st i_s i_v in

    let aux (i:_)
      : Lemma (ensures (related_store_entry_opt (Seq.index st_ i) (Seq.index i_st_ i)))
      = related_root_inv ();
        if i <> i_s then
        begin
          assert (Seq.index st_ i == Seq.index st i);
          assert (IS.identical_except i_st i_st_ i_s);

          eliminate forall s'. s' <> i_s ==> IS.get_slot i_st s' = IS.get_slot i_st_ s'
          with i
        end
    in
    forall_intro aux;
    ()

let init_store_related (tid: AT.tid) (i_tid: i_tid)
  : Lemma (requires (related_tid tid i_tid))
          (ensures (let tsm = init_thread_state_model tid in
                    let i_tsm = IV.init_thread_state i_vcfg i_tid in
                    related_store tsm.store i_tsm.IV.st))
  = let tsm = init_thread_state_model tid in
    let st = tsm.store in
    let i_st = IV.init_store i_vcfg i_tid in

    let empty_st: TSM.contents = Seq.create (U16.v AT.store_size) None in
    let i_empty_st = IS.empty_store i_vcfg in

    empty_store_related ();
    assert (related_store empty_st i_empty_st);

    if i_tid = 0 then
    begin

      (* state of initial tsm before the madd *)
      let _tsm = {
        thread_id = tid;
        failed = false;
        store = Seq.create (U16.v AT.store_size) None;
        clock = 0uL;
        epoch_hashes = initial_epoch_hashes;
        processed_entries = Seq.empty;
        app_results = Seq.empty;
        last_verified_epoch = None
      } in

      let s = U16.zero in
      let i_s = 0 in
      assert (related_slot s i_s);

      let rk = root_key in
      let v = init_value rk in

      let i_rk: GK.key app = GK.IntK Zeta.BinTree.Root in
      let i_v = R.init_value i_rk in

      assert (related_val v i_v);

      assert (tsm == madd_to_store_root _tsm U16.zero (init_value root_key));
      related_madd_to_store_root _tsm i_empty_st s i_s v i_v;

      ()
    end
    else
    begin
      assert (i_st == i_empty_st);
      assert (st == empty_st);
      ()
    end

let init_state_related (tid: AT.tid) (i_tid: i_tid)
  : Lemma (requires (related_tid tid i_tid))
          (ensures (let tsm = init_thread_state_model tid in
                    let i_tsm = IV.init_thread_state i_vcfg i_tid in
                    related_tsm tsm i_tsm))
  = let tsm = init_thread_state_model tid in
    let i_tsm = IV.init_thread_state i_vcfg i_tid in

    // both models are in not failed state
    assert (not tsm.failed /\ i_tsm.IV.valid);

    // thread ids are equal by construction
    assert (related_tid tsm.thread_id i_tsm.IV.tid);
    related_timestamp_zero ();
    assert (related_timestamp tsm.clock i_tsm.IV.clock);

    init_store_related tid i_tid

let init_tsm_spec_rel_base (tid: AT.tid)
  : Lemma (ensures (spec_rel_base (init_thread_state_model tid)))
  = let tsm = init_thread_state_model tid in
    let i_tid = lift_tid tsm.thread_id in
    init_state_related tid i_tid;
    ()

let length tsm = Seq.length tsm.processed_entries

let prev (tsm: valid_tsm {length tsm > 0})
  : thread_state_model
  = let i = length tsm - 1 in
    run tsm.thread_id (SA.prefix tsm.processed_entries i)

let last_entry (tsm: valid_tsm {length tsm > 0})
  : GTot (e:_ { valid_log_entry e })
  = let i = length tsm - 1 in
    Seq.index tsm.processed_entries i

(* the prev of a valid tsm is also valid *)
let valid_prev (tsm: valid_tsm {length tsm > 0} )
  : Lemma (ensures (valid (prev tsm)))
          [SMTPat (prev tsm)]
  = let _tsm = prev tsm in
    let e = last_entry tsm in

    let l = tsm.processed_entries in
    let i = length tsm - 1 in
    let _l = SA.prefix l i in

    // from definition of valid_tsm and run
    assert (tsm == run tsm.thread_id tsm.processed_entries);
    assert (tsm == verify_step_model _tsm e);

    // from last assert, _tsm cannot be in failed state
    assert (not _tsm.failed);

    // definition of prev
    assert (_tsm == run tsm.thread_id _l);

    run_implies_processed_entries tsm.thread_id _l;
    assert (_tsm.processed_entries == _l);

    ()

let lemma_prev_log_prefix (tsm: valid_tsm {length tsm > 0 })
  : Lemma (ensures (let _tsm = prev tsm in
                    let l = tsm.processed_entries in
                    let i = length tsm - 1 in
                    _tsm.processed_entries == SA.prefix l i))
          [SMTPat (prev tsm)]
  = let _tsm = prev tsm in
    let e = last_entry tsm in

    let l = tsm.processed_entries in
    let i = Seq.length l - 1 in
    let _l = SA.prefix l i in

    // from definition of valid_tsm and run
    assert (tsm == run tsm.thread_id tsm.processed_entries);
    assert (tsm == verify_step_model _tsm e);

    // from last assert, _tsm cannot be in failed state
    assert (not _tsm.failed);

    // definition of prev
    assert (_tsm == run tsm.thread_id _l);

    run_implies_processed_entries tsm.thread_id _l;
    assert (_tsm.processed_entries == _l);

    ()

let spec_rel_base_snoc (tsm: valid_tsm {length tsm > 0})
  : Lemma (requires (let _tsm = prev tsm in
                     spec_rel_base _tsm))
          (ensures (spec_rel_base tsm))
  = let _tsm = prev tsm in
    let e = last_entry tsm in
    assert (tsm == verify_step_model _tsm e);
    lemma_verify_step_model_spec_rel_base _tsm e

let rec valid_implies_spec_rel_base (tsm: valid_tsm)
  : Lemma (ensures (spec_rel_base tsm))
          (decreases (length tsm))
          [SMTPat (valid tsm)]
  = let tid = tsm.thread_id in
    let i_tid = lift_tid tid in
    if length tsm = 0 then
      init_tsm_spec_rel_base tid
    else
    begin
      let _tsm = prev tsm in
      valid_implies_spec_rel_base _tsm;
      spec_rel_base_snoc tsm
    end

module GT = Zeta.Generic.Thread

let init_add_set_empty (tsm: valid_tsm {length tsm = 0}) (ep: epoch_id)
  : Lemma (ensures (add_set tsm (lift_epoch ep) == Zeta.MultiSet.empty))
  = let i_ep = lift_epoch ep in
    let tid = tsm.thread_id in
    let l = tsm.processed_entries in

    assert (tsm == init_thread_state_model tid);

    let i_tl = to_ilog tsm in
    assert (GT.length i_tl = 0);

    let add_seq = GT.add_seq i_ep i_tl in

    GT.add_seq_empty i_ep i_tl;
    assert (Seq.length add_seq = 0);

    let open Zeta.MultiSetHashDomain in
    Zeta.MultiSet.zero_length_implies_empty #_ #(ms_hashfn_dom_cmp app) add_seq

let init_hadd_correct (tsm: valid_tsm {length tsm = 0}) (ep: epoch_id)
  : Lemma (ensures (let i_ep = lift_epoch ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hadd = ms_hashfn (add_set tsm i_ep)))
  = let i_ep = lift_epoch ep in
    init_add_set_empty tsm ep;
    lemma_hashfn_empty ();
    assert (ms_hashfn (add_set tsm i_ep) == HA.initial_hash);
    assert (tsm.epoch_hashes == initial_epoch_hashes);
    ()

let is_blum_add e =
  let open T in
  match e with
  | AddB _ _ _ _ -> true
  | _ -> false

let blum_add_timestamp (e:_ {is_blum_add e})
  = let open T in
    match e with
    | AddB _  t _ _ -> t

let blum_add_tid (e: _ {is_blum_add e})
  = let open T in
    match e with
    | AddB _ _ tid _ -> tid

let blum_add_record (e:_ {is_blum_add e})
  = let open T in
    match e with
    | AddB _ _ _ r -> r

let blum_add_slot (e:_ {is_blum_add e})
  = let open T in
    match e with
    | AddB s _ _ _ -> s

#push-options "--fuel 2 --ifuel 1 --z3rlimit_factor 4 --query_stats"
#restart-solver

let epoch_hashes_unchanged_addm (tsm: thread_state_model) (e: s_log_entry {T.AddM? e})
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    not tsm_.failed ==> tsm.epoch_hashes == tsm_.epoch_hashes))
  = ()

let epoch_hashes_unchanged_evictm (tsm: thread_state_model) (e: s_log_entry {T.EvictM? e})
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    not tsm_.failed ==> tsm.epoch_hashes == tsm_.epoch_hashes))
  = ()

let epoch_hashes_unchanged_next_epoch (tsm: thread_state_model) (e: s_log_entry {T.NextEpoch? e})
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    not tsm_.failed ==> tsm.epoch_hashes == tsm_.epoch_hashes))
  = admit()

let epoch_hashes_unchanged_verify_epoch
    (tsm: thread_state_model)
    (e: s_log_entry {T.VerifyEpoch? e})
    (ep: epoch_id)
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    let eh_ = Map.sel tsm_.epoch_hashes ep in
                    not tsm_.failed ==> (eh.hadd == eh_.hadd /\
                                         eh.hevict == eh_.hevict)))
  = ()

#pop-options

let runapp_does_not_change_epoch_hashes (tsm: thread_state_model) (pl: T.runApp_payload)
  : Lemma (ensures (let tsm_ = runapp tsm pl in
                    not tsm_.failed ==> tsm_.epoch_hashes == tsm.epoch_hashes))
  = let tsm_ = runapp tsm pl in
    if not tsm_.failed then
    begin
      assert (Map.contains app.A.tbl pl.fid);
      match AT.spec_app_parser pl.fid pl.rest.ebytes with
      | Some ((arg, slots), len) ->
        assert (len = U32.v pl.rest.len);
        let fsig = Map.sel app.A.tbl pl.fid in
        match read_slots tsm slots with
        | Some recs ->
          let res = fsig.f arg recs in
          match res with
          | (_, res, out_vals) ->
            let tsm1 = {tsm with app_results=Seq.Properties.snoc tsm.app_results (| pl.fid, arg, recs, res |)} in
            assert (tsm1.epoch_hashes == tsm.epoch_hashes);
            assert (tsm_ == write_slots tsm1 slots out_vals);
            write_slots_non_store_prop tsm1 slots out_vals;
            assert (tsm_.epoch_hashes == tsm1.epoch_hashes);
            ()
    end

let epoch_hashes_unchanged_runapp
  (tsm: thread_state_model)
  (e: s_log_entry {T.RunApp? e})
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    not tsm_.failed ==> tsm.epoch_hashes == tsm_.epoch_hashes))
  = let T.RunApp p = e in
    runapp_does_not_change_epoch_hashes tsm p

let update_hadd_unchanged_hevict (tsm: thread_state_model)
                                 (ep: epoch_id)
                                 (r: T.record)
                                 (t: T.timestamp)
                                 (tid: T.thread_id)
                                 (epi: epoch_id)
  : Lemma (ensures (let tsm_ = update_hadd tsm ep r t tid in
                    let eh = Map.sel tsm.epoch_hashes epi in
                    let eh_ = Map.sel tsm.epoch_hashes epi in
                    eh.hevict == eh_.hevict))
  = ()

let update_hevict_unchanged_hadd (tsm: thread_state_model)
                                 (ep: epoch_id)
                                 (r: T.record)
                                 (t: T.timestamp)
                                 (tid: T.thread_id)
                                 (epi: epoch_id)
  : Lemma (ensures (let tsm_ = update_hevict tsm ep r t tid in
                    let eh = Map.sel tsm.epoch_hashes epi in
                    let eh_ = Map.sel tsm.epoch_hashes epi in
                    eh.hadd == eh_.hadd))
  = ()

let evict_hashes_unchanged_addb (tsm: thread_state_model) (e: s_log_entry {is_blum_add e}) (ep: epoch_id)
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    let eh_ = Map.sel tsm_.epoch_hashes ep in
                    not tsm_.failed ==> eh.hevict == eh_.hevict))
  = let tsm_ = verify_step_model tsm e in
    let eh = Map.sel tsm.epoch_hashes ep in
    let eh_ = Map.sel tsm_.epoch_hashes ep in

    let s = blum_add_slot e in
    let t = blum_add_timestamp e in
    let tid = blum_add_tid e in
    let (k,v) = blum_add_record e in

    if not tsm_.failed then
    begin
      let tsm1 = update_hadd tsm (epoch_of_timestamp t) (k,v) t tid in
      assert (tsm_.epoch_hashes == tsm1.epoch_hashes);
      update_hadd_unchanged_hevict tsm (epoch_of_timestamp t) (k,v) t tid ep
    end

let add_hashes_unchanged_evictb (tsm: thread_state_model) (e: s_log_entry {T.EvictB? e}) (ep: epoch_id)
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    let eh_ = Map.sel tsm_.epoch_hashes ep in
                    not tsm_.failed ==> eh.hadd == eh_.hadd))
  = ()

let add_hashes_unchanged_evictbm (tsm: thread_state_model) (e: s_log_entry {T.EvictBM? e}) (ep: epoch_id)
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    let eh_ = Map.sel tsm_.epoch_hashes ep in
                    not tsm_.failed ==> eh.hadd == eh_.hadd))
  = ()

(* the add-set hashes remain unchanged with any operation other than addb/addbapp *)
let add_hashes_unchanged_non_addb
  (tsm: thread_state_model)
  (e: s_log_entry {not (is_blum_add e)})
  (ep: epoch_id)
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    let eh_ = Map.sel tsm_.epoch_hashes ep in
                    not tsm_.failed ==> eh.hadd == eh_.hadd))
  = let open T in
    match e with
    | AddM _ _ _ -> epoch_hashes_unchanged_addm tsm e
    | EvictM _ -> epoch_hashes_unchanged_evictm tsm e
    | EvictB _ -> add_hashes_unchanged_evictb tsm e ep
    | EvictBM _ -> add_hashes_unchanged_evictbm tsm e ep
    | NextEpoch -> epoch_hashes_unchanged_next_epoch tsm e
    | VerifyEpoch -> epoch_hashes_unchanged_verify_epoch tsm e ep
    | RunApp _ -> epoch_hashes_unchanged_runapp tsm e

let hadd_correct_snoc_non_addb (tsm: valid_tsm {length tsm > 0}) (ep: epoch_id)
  : Lemma (requires (let i_ep = lift_epoch ep in
                     let _tsm = prev tsm in
                     let _eh = Map.sel _tsm.epoch_hashes ep in
                     let e = last_entry tsm in
                     not (is_blum_add e) /\
                     _eh.hadd = ms_hashfn (add_set _tsm i_ep)))
          (ensures (let i_ep = lift_epoch ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hadd = ms_hashfn (add_set tsm i_ep)))
  = let i = length tsm - 1 in
    let e = last_entry tsm in
    let eh = Map.sel tsm.epoch_hashes ep in

    let _tsm = prev tsm in
    let _eh = Map.sel _tsm.epoch_hashes ep in

    // add hashes are unchanged for non-addb entries
    add_hashes_unchanged_non_addb _tsm e ep;
    assert (eh.hadd == _eh.hadd);

    let i_ep = lift_epoch ep in
    let i_e = lift_log_entry e in
    let i_tl = to_ilog tsm in
    let _i_tl = to_ilog _tsm in

    // last entry is not a blum add in spec-level
    assert (not (GT.is_blum_add_ep i_ep i_tl i));

    // the add-seq remains unchanged
    GT.add_seq_snoc i_ep  i_tl;
    assert (GT.add_seq i_ep i_tl == GT.add_seq i_ep _i_tl);

    ()

let haddevict_unchanged_addb_diff_epoch
  (tsm: thread_state_model)
  (e: _ {is_blum_add e})
  (ep: epoch_id)
  : Lemma (requires (epoch_of_timestamp (blum_add_timestamp e) <> ep))
          (ensures (let tsm_ = verify_step_model tsm e in
                    let eh_ = Map.sel tsm_.epoch_hashes ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hadd == eh_.hadd /\
                    eh.hevict == eh_.hevict))
  = ()

let hadd_change_addb
  (tsm: thread_state_model)
  (e: _ {is_blum_add e})
  (ep: epoch_id)
  : Lemma (requires (epoch_of_timestamp (blum_add_timestamp e) = ep))
          (ensures (let tsm_ = verify_step_model tsm e in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    let eh_ = Map.sel tsm_.epoch_hashes ep in
                    let (k, v) = blum_add_record e in
                    let t = blum_add_timestamp e in
                    let tid = blum_add_tid e in
                    not tsm_.failed ==>
                    eh_.hadd == update_hash_value eh.hadd (k,v) t tid))
  = ()

let hadd_correct_snoc_addb_diff_epoch (tsm: valid_tsm {length tsm > 0}) (ep: epoch_id)
  : Lemma (requires (let i_ep = lift_epoch ep in
                     let _tsm = prev tsm in
                     let _eh = Map.sel _tsm.epoch_hashes ep in
                     let e = last_entry tsm in
                     is_blum_add e /\
                     _eh.hadd = ms_hashfn (add_set _tsm i_ep) /\
                     epoch_of_timestamp (blum_add_timestamp e) <> ep))
          (ensures (let i_ep = lift_epoch ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hadd = ms_hashfn (add_set tsm i_ep)))
  = let i = length tsm - 1 in
    let i_ep = lift_epoch ep in
    let e = last_entry tsm in
    let eh = Map.sel tsm.epoch_hashes ep in
    let i_e = lift_log_entry e in
    let i_tl = to_ilog tsm in

    let i_tsm = to_i_tsm tsm in
    assert (related_tsm tsm i_tsm);

    let _tsm = prev tsm in
    let _i_tsm = to_i_tsm _tsm in
    let _eh = Map.sel _tsm.epoch_hashes ep in
    let _i_tl = to_ilog _tsm in

    assert (related_tsm _tsm _i_tsm);
    assert (_i_tl == GT.prefix i_tl i);

    let i_be = GT.blum_add_elem i_tl i in

    let t = blum_add_timestamp e in
    let tid = blum_add_tid e in
    let (k, v) = blum_add_record e in
    let s_be: s_dom =
      let open Zeta.Steel.MultiSetHash in
      { r = (k,v); t ; tid } in
    assert (related_msdom s_be i_be);

    let ep' = epoch_of_timestamp t in
    assert (ep' <> ep);

    assert (related_timestamp t i_be.t);
    related_timestamp_epoch t i_be.t;

    // since ep' <> ep, blum_add_seq is unchanged
    GT.add_seq_snoc i_ep i_tl;
    assert (GT.add_seq i_ep i_tl == GT.add_seq i_ep _i_tl);
    assert (add_set tsm i_ep == add_set _tsm i_ep);

    haddevict_unchanged_addb_diff_epoch _tsm e ep

let hadd_correct_snoc_addb_same_epoch (tsm: valid_tsm {length tsm > 0}) (ep: epoch_id)
  : Lemma (requires (let i_ep = lift_epoch ep in
                     let _tsm = prev tsm in
                     let _eh = Map.sel _tsm.epoch_hashes ep in
                     let e = last_entry tsm in
                     is_blum_add e /\
                     _eh.hadd = ms_hashfn (add_set _tsm i_ep) /\
                     epoch_of_timestamp (blum_add_timestamp e) = ep))
          (ensures (let i_ep = lift_epoch ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hadd = ms_hashfn (add_set tsm i_ep)))
  = let i = length tsm - 1 in
    let i_ep = lift_epoch ep in
    let e = last_entry tsm in
    let eh = Map.sel tsm.epoch_hashes ep in
    let i_e = lift_log_entry e in
    let i_tl = to_ilog tsm in

    let i_tsm = to_i_tsm tsm in
    assert (related_tsm tsm i_tsm);

    let _tsm = prev tsm in
    let _i_tsm = to_i_tsm _tsm in
    let _eh = Map.sel _tsm.epoch_hashes ep in
    let _i_tl = to_ilog _tsm in

    assert (related_tsm _tsm _i_tsm);
    assert (_i_tl == GT.prefix i_tl i);

    let i_be = GT.blum_add_elem i_tl i in

    let t = blum_add_timestamp e in
    let tid = blum_add_tid e in
    let (k, v) = blum_add_record e in
    let s_be: s_dom =
      let open Zeta.Steel.MultiSetHash in
      { r = (k,v); t ; tid } in
    assert (related_msdom s_be i_be);

    assert (related_timestamp t i_be.t);
    related_timestamp_epoch t i_be.t;

    GT.add_seq_snoc i_ep i_tl;
    assert (GT.is_blum_add_ep i_ep i_tl i);

    assert (GT.add_seq i_ep i_tl == SA.append1 (GT.add_seq i_ep _i_tl) i_be);
    let open Zeta.MultiSetHashDomain in
    Zeta.MultiSet.seq2mset_add_elem #_ #(ms_hashfn_dom_cmp app) (GT.add_seq i_ep _i_tl) i_be;
    assert (add_set tsm i_ep == MS.add_elem (add_set _tsm i_ep) i_be);

    hadd_change_addb _tsm e ep;
    lemma_update (add_set _tsm i_ep) i_be s_be;
    ()

let hadd_correct_snoc (tsm: valid_tsm {length tsm > 0}) (ep: epoch_id)
  : Lemma (requires (let i_ep = lift_epoch ep in
                     let _tsm = prev tsm in
                     let _eh = Map.sel _tsm.epoch_hashes ep in
                     _eh.hadd = ms_hashfn (add_set _tsm i_ep)))
          (ensures (let i_ep = lift_epoch ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hadd = ms_hashfn (add_set tsm i_ep)))
  = let e = last_entry tsm in

    if is_blum_add e then
      if epoch_of_timestamp (blum_add_timestamp e) = ep then
        hadd_correct_snoc_addb_same_epoch tsm ep
      else
        hadd_correct_snoc_addb_diff_epoch tsm ep
    else
      hadd_correct_snoc_non_addb tsm ep

let rec valid_implies_hadd_correct (tsm: valid_tsm) (ep: epoch_id)
  : Lemma (ensures (let i_ep = lift_epoch ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hadd = ms_hashfn (add_set tsm i_ep)))
          (decreases (length tsm))
  = if length tsm = 0 then
      init_hadd_correct tsm ep
    else
    begin
      let _tsm = prev tsm in
      valid_implies_hadd_correct _tsm ep;
      hadd_correct_snoc tsm ep
    end

let init_evict_set_empty (tsm: valid_tsm {length tsm = 0}) (ep: epoch_id)
  : Lemma (ensures (evict_set tsm (lift_epoch ep) == Zeta.MultiSet.empty))
  = let i_ep = lift_epoch ep in
    let tid = tsm.thread_id in
    let l = tsm.processed_entries in

    assert (tsm == init_thread_state_model tid);

    let i_tl = to_ilog tsm in
    assert (GT.length i_tl = 0);

    let evict_seq = GT.evict_seq i_ep i_tl in
    GT.evict_seq_empty i_ep i_tl;
    assert (Seq.length evict_seq = 0);

    let open Zeta.MultiSetHashDomain in
    Zeta.MultiSet.zero_length_implies_empty #_ #(ms_hashfn_dom_cmp app) evict_seq

let init_hevict_correct (tsm: valid_tsm {length tsm = 0}) (ep: epoch_id)
  : Lemma (ensures (let i_ep = lift_epoch ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hevict = ms_hashfn (evict_set tsm i_ep)))
  = let i_ep = lift_epoch ep in
    init_evict_set_empty tsm ep;
    lemma_hashfn_empty ();
    ()

let is_blum_evict e =
  let open T in
  match e with
  | EvictB _ -> true
  | EvictBM _ -> true
  | _ -> false

let blum_evict_timestamp (e:_ {is_blum_evict e})
  = let open T in
    match e with
    | EvictB p -> p.t
    | EvictBM p -> p.t

let blum_evict_slot (e:_ {is_blum_evict e})
  = let open T in
    match e with
    | EvictB p -> p.s
    | EvictBM p -> p.s

let evict_hashes_unchanged_non_evict
  (tsm: thread_state_model)
  (e: s_log_entry { not (is_blum_evict e) })
  (ep: epoch_id)
  : Lemma (ensures (let tsm_ = verify_step_model tsm e in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    let eh_ = Map.sel tsm_.epoch_hashes ep in
                    not tsm_.failed ==> eh.hevict == eh_.hevict))
  = let open T in
    match e with
    | AddM _ _ _ -> epoch_hashes_unchanged_addm tsm e
    | AddB _ _ _ _ -> evict_hashes_unchanged_addb tsm e ep
    | EvictM _ -> epoch_hashes_unchanged_evictm tsm e
    | NextEpoch -> epoch_hashes_unchanged_next_epoch tsm e
    | VerifyEpoch -> epoch_hashes_unchanged_verify_epoch tsm e ep
    | RunApp _ -> epoch_hashes_unchanged_runapp tsm e

let hevict_change_evictb
  (tsm: thread_state_model)
  (e:_ {T.EvictB? e \/ T.EvictBM? e})
  : Lemma (requires (let s = blum_evict_slot e in
                     let t = blum_evict_timestamp e in
                     check_slot_bounds s /\
                     sat_evictb_checks tsm s t))
          (ensures (let s = blum_evict_slot e in
                    let t = blum_evict_timestamp e in
                    let ep = epoch_of_timestamp t in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    let Some r = get_entry tsm s in
                    let tsm_ = verify_step_model tsm e in
                    let eh_ = Map.sel tsm_.epoch_hashes ep in
                    not tsm_.failed ==>
                    eh_.hevict == update_hash_value eh.hevict (r.key, r.value) t tsm.thread_id))
  = ()

let hevict_correct_snoc_non_evictb
  (tsm: valid_tsm {length tsm > 0}) (ep: epoch_id)
  : Lemma (requires (let i_ep = lift_epoch ep in
                     let _tsm = prev tsm in
                     let _eh = Map.sel _tsm.epoch_hashes ep in
                     let e = last_entry tsm in
                     not (is_blum_evict e) /\
                     _eh.hevict = ms_hashfn (evict_set _tsm i_ep)))
          (ensures (let i_ep = lift_epoch ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hevict = ms_hashfn (evict_set tsm i_ep)))
  = let i = length tsm - 1 in
    let e = last_entry tsm in
    let eh = Map.sel tsm.epoch_hashes ep in

    let _tsm = prev tsm in
    let _eh = Map.sel _tsm.epoch_hashes ep in

    evict_hashes_unchanged_non_evict _tsm e ep;
    assert (eh.hevict == _eh.hevict);

    let i_ep = lift_epoch ep in
    let i_e = lift_log_entry e in
    let i_tl = to_ilog tsm in
    let _i_tl = to_ilog _tsm in

    assert (not (GT.is_blum_evict_ep i_ep i_tl i));

    GT.evict_seq_snoc i_ep i_tl;
    assert (GT.evict_seq i_ep i_tl == GT.evict_seq i_ep _i_tl);
    ()

module MSD = Zeta.MultiSetHashDomain

let blum_evict_elem (tsm: valid_tsm {length tsm > 0 /\ is_blum_evict (last_entry tsm)})
  : GTot (Zeta.Steel.MultiSetHash.s_dom)
  = let i = length tsm - 1 in
    let e = last_entry tsm in
    let s = blum_evict_slot e in
    let t = blum_evict_timestamp e in
    let _tsm = prev tsm in
    let Some r0 = get_entry _tsm s in
    let r = (r0.key, r0.value) in
    let s_be: s_dom =
      let open Zeta.Steel.MultiSetHash in
      { r ; t; tid = tsm.thread_id } in
    s_be

#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 3 --query_stats"

let related_blum_evict_elem (tsm: valid_tsm {spec_rel_base tsm /\ length tsm > 0})
  : Lemma (requires (is_blum_evict (last_entry tsm)))
          (ensures (let i = length tsm - 1 in
                    let i_tl = to_ilog tsm in
                    let i_be = GT.blum_evict_elem i_tl i in
                    let s_be = blum_evict_elem tsm in
                    Zeta.Steel.MultiSetHash.related_msdom s_be i_be))
  = let i = length tsm - 1 in
    let e = last_entry tsm in
    let i_tl = to_ilog tsm in
    let i_be = GT.blum_evict_elem i_tl i in
    let s_be = blum_evict_elem tsm in

    let _tsm = prev tsm in
    let _st = _tsm.store in

    let _i_tsm = to_i_tsm _tsm in
    let _i_st = _i_tsm.IV.st in
    assert (related_store _st _i_st);

    let MSD.MHDom i_r i_t i_j = i_be in

    let s = blum_evict_slot e in

    let Some se = get_slot _st s in
    assert (s_be.r = (se.key, se.value));

    let i_e = GT.index i_tl i in
    let i_s = GV.evict_slot i_e in
    assert (related_log_entry e i_e);
    assert (related_slot s i_s);

    eliminate forall i. related_store_entry_opt (Seq.index _st i) (Seq.index _i_st i)
    with i_s;

    let Some ie = Seq.index _i_st i_s in
    assert (related_store_entry_opt (Some se) (Some ie));
    assert (related_store_entry se ie);
    let IS.VStoreE i_r2 _ _ _ _ = ie in

    assert (related_record (se.key, se.value) i_r2);
    assert (related_record s_be.r i_r2);
    assert (i_r2 = i_r);
    ()

#pop-options

#push-options "--fuel 1 --ifuel 1 --query_stats"

let hevict_correct_snoc_evictb_same_epoch
  (tsm: valid_tsm {length tsm > 0})
  (ep: epoch_id)
  : Lemma (requires (let i_ep = lift_epoch ep in
                     let _tsm = prev tsm in
                     let _eh = Map.sel _tsm.epoch_hashes ep in
                     let e = last_entry tsm in
                     is_blum_evict e /\
                     _eh.hevict = ms_hashfn (evict_set _tsm i_ep) /\
                     epoch_of_timestamp (blum_evict_timestamp e) = ep))
           (ensures (let i_ep = lift_epoch ep in
                     let eh = Map.sel tsm.epoch_hashes ep in
                     eh.hevict = ms_hashfn (evict_set tsm i_ep)))
 = let i = length tsm - 1 in
   let i_ep = lift_epoch ep in
   let e = last_entry tsm in
   let eh = Map.sel tsm.epoch_hashes ep in
   let i_e = lift_log_entry e in

   let i_tl = to_ilog tsm in
   let i_tsm = to_i_tsm tsm in
   assert (related_tsm tsm i_tsm);

   let _tsm = prev tsm in
   let _i_tsm = to_i_tsm _tsm in
   let _eh = Map.sel _tsm.epoch_hashes ep in
   let _i_tl = to_ilog _tsm in
   assert (related_tsm _tsm _i_tsm);
   assert (_i_tl = GT.prefix i_tl i);

   let i_be = GT.blum_evict_elem i_tl i in
   let t = blum_evict_timestamp e in
   let tid = tsm.thread_id in
   let s = blum_evict_slot e in
   let i_s = lift_slot s in
   assert (i_s = GV.evict_slot i_e);

   assert (tsm == verify_step_model _tsm e);

   let s_be = blum_evict_elem tsm in

   let MSD.MHDom i_r i_t i_j = i_be in
   related_blum_evict_elem tsm;
   related_timestamp_epoch t i_t;
   assert (GT.is_blum_evict_ep i_ep i_tl i);
   GT.evict_seq_snoc i_ep i_tl;

   assert (GT.evict_seq i_ep i_tl == SA.append1 (GT.evict_seq i_ep _i_tl) i_be);
   let open Zeta.MultiSetHashDomain in
   Zeta.MultiSet.seq2mset_add_elem #_ #(ms_hashfn_dom_cmp app) (GT.evict_seq i_ep _i_tl) i_be;
   assert (evict_set tsm i_ep == MS.add_elem (evict_set _tsm i_ep) i_be);

   hevict_change_evictb _tsm e;
   lemma_update (evict_set _tsm i_ep) i_be s_be;
   ()

#pop-options

let haddevict_unchanged_evictb_diff_epoch
  (tsm: thread_state_model)
  (e: _ {is_blum_evict e})
  (ep: epoch_id)
  : Lemma (requires (epoch_of_timestamp (blum_evict_timestamp e) <> ep))
          (ensures (let tsm_ = verify_step_model tsm e in
                    let eh_ = Map.sel tsm_.epoch_hashes ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hadd == eh_.hadd /\
                    eh.hevict == eh_.hevict))
  = ()

#push-options "--fuel 1 --ifuel 1 --query_stats"

let hevict_correct_snoc_evictb_diff_epoch (tsm: valid_tsm {length tsm > 0}) (ep: epoch_id)
  : Lemma (requires (let i_ep = lift_epoch ep in
                     let _tsm = prev tsm in
                     let _eh = Map.sel _tsm.epoch_hashes ep in
                     let e = last_entry tsm in
                     is_blum_evict e /\
                     _eh.hevict = ms_hashfn (evict_set _tsm i_ep) /\
                     epoch_of_timestamp (blum_evict_timestamp e) <> ep))
          (ensures (let i_ep = lift_epoch ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hevict = ms_hashfn (evict_set tsm i_ep)))
  = let i = length tsm - 1 in
    let i_ep = lift_epoch ep in
    let e = last_entry tsm in
    let eh = Map.sel tsm.epoch_hashes ep in

    let i_e = lift_log_entry e in
    let i_tl = to_ilog tsm in
    let i_tsm = to_i_tsm tsm in
    assert (related_tsm tsm i_tsm);

    let _tsm = prev tsm in
    let _i_tsm = to_i_tsm _tsm in
    let _eh = Map.sel _tsm.epoch_hashes ep in
    let _i_tl = to_ilog _tsm in

    assert (related_tsm _tsm _i_tsm);
    assert (_i_tl == GT.prefix i_tl i);
    assert (i_e = GT.index i_tl i);

    assert (GT.is_blum_evict i_tl i);
    let i_be = GT.blum_evict_elem i_tl i in
    let t = blum_evict_timestamp e in
    let ep' = epoch_of_timestamp t in
    assert (ep <> ep');

    assert (related_timestamp t i_be.MSD.t);
    related_timestamp_epoch t i_be.MSD.t;

    assert (~ (GT.is_blum_evict_ep i_ep i_tl i));
    GT.evict_seq_snoc i_ep i_tl;
    assert (GT.evict_seq i_ep i_tl == GT.evict_seq i_ep _i_tl);
    assert (evict_set tsm i_ep == evict_set _tsm i_ep);

    haddevict_unchanged_evictb_diff_epoch _tsm e ep

#pop-options

let hevict_correct_snoc (tsm: valid_tsm {length tsm > 0}) (ep: epoch_id)
  : Lemma (requires (let i_ep = lift_epoch ep in
                     let _tsm = prev tsm in
                     let _eh = Map.sel _tsm.epoch_hashes ep in
                     _eh.hevict = ms_hashfn (evict_set _tsm i_ep)))
          (ensures (let i_ep = lift_epoch ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hevict = ms_hashfn (evict_set tsm i_ep)))
  = let e = last_entry tsm in

    if is_blum_evict e then
      if epoch_of_timestamp (blum_evict_timestamp e) = ep then
        hevict_correct_snoc_evictb_same_epoch tsm ep
      else
        hevict_correct_snoc_evictb_diff_epoch tsm ep
    else
      hevict_correct_snoc_non_evictb tsm ep

let rec valid_implies_hevict_correct (tsm: valid_tsm) (ep: epoch_id)
  : Lemma (ensures (let i_ep = lift_epoch ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hevict = ms_hashfn (evict_set tsm i_ep)))
          (decreases (length tsm))
  = if length tsm = 0 then
      init_hevict_correct tsm ep
    else
    begin
      let _tsm = prev tsm in
      valid_implies_hevict_correct _tsm ep;
      hevict_correct_snoc tsm ep
    end

let valid_implies_epoch_hashes_correct (tsm: valid_tsm)
  : Lemma (ensures (forall (ep: epoch_id). let i_ep = lift_epoch ep in
                                      let eh = Map.sel tsm.epoch_hashes ep in
                                      eh.hadd = ms_hashfn (add_set tsm i_ep) /\
                                      eh.hevict = ms_hashfn (evict_set tsm i_ep)))
  = let aux (ep:_)
      : Lemma (ensures (let i_ep = lift_epoch ep in
                        let eh = Map.sel tsm.epoch_hashes ep in
                        eh.hadd = ms_hashfn (add_set tsm i_ep) /\
                        eh.hevict = ms_hashfn (evict_set tsm i_ep)))
      = let i_ep = lift_epoch ep in
        let eh = Map.sel tsm.epoch_hashes ep in
        valid_implies_hadd_correct tsm ep;
        valid_implies_hevict_correct tsm ep
    in
    forall_intro aux

let valid_implies_spec_rel (tsm: valid_tsm)
  : Lemma (ensures (spec_rel tsm))
  = valid_implies_epoch_hashes_correct tsm

let valid_hadd_prop (ep: TSM.epoch_id) (tsm: valid_tsm)
  : Lemma (ensures (let i_ep = lift_epoch ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hadd = ms_hashfn (add_set tsm i_ep)))
  = valid_implies_epoch_hashes_correct tsm;
    eliminate forall (ep: epoch_id). let i_ep = lift_epoch ep in
                                let eh = Map.sel tsm.epoch_hashes ep in
                                eh.hadd = ms_hashfn (add_set tsm i_ep) /\
                                eh.hevict = ms_hashfn (evict_set tsm i_ep)
    with ep;
    ()

let valid_hevict_prop (ep: TSM.epoch_id) (tsm: valid_tsm)
  : Lemma (ensures (let i_ep = lift_epoch ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hevict = ms_hashfn (evict_set tsm i_ep)))
  = valid_implies_epoch_hashes_correct tsm;
    eliminate forall (ep: epoch_id). let i_ep = lift_epoch ep in
                                let eh = Map.sel tsm.epoch_hashes ep in
                                eh.hadd = ms_hashfn (add_set tsm i_ep) /\
                                eh.hevict = ms_hashfn (evict_set tsm i_ep)
    with ep;
    ()

let run_props (tid: AT.tid) (l: s_log)
  : Lemma (ensures (let tsm = run tid l in
                    (not tsm.failed) ==> (valid tsm /\
                                         tsm.thread_id = tid /\
                                         tsm.processed_entries == l)))
  = run_implies_thread_id tid l;
    run_implies_processed_entries tid l;
    run_implies_valid tid l
