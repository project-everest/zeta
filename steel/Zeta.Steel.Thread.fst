module Zeta.Steel.Thread

open Zeta.Steel.LogRel

module A = Zeta.App
module AS = Zeta.AppSimulate
module IV = Zeta.Intermediate.Verifier
module SA = Zeta.SeqAux
module T = Zeta.Steel.FormatsManual

let state (tl: verifiable_log)
  : tsm:valid_tsm {let t,l = tl in
                   tsm.processed_entries == l /\
                   tsm.thread_id == t}
  = let tid, l = tl in
    let tsm = run tid l in
    run_props tid l;
    tsm

let to_tsm = state

let is_appfn (tl: verifiable_log) (i: seq_index tl)
  = let e = index tl i in
    let open T in
    match e with
    | RunApp _ -> true
    | _ -> false

let prefix_base (tl: verifiable_log) (i:nat {i <= length tl})
  : tlog
  = let tid,l = tl in
    tid, SA.prefix l i

let prefix_verifiable_snoc (tl: verifiable_log { length tl > 0 })
  : Lemma (ensures (let i = length tl - 1 in
                    let tl' = prefix_base tl i in
                    verifiable tl'))
  = ()

let rec prefix_verifiable (tl: verifiable_log) (i:nat {i <= length tl})
  : Lemma (ensures (verifiable (prefix_base tl i)))
          (decreases (length tl))
          [SMTPat (prefix_base tl i)]
  = if i < length tl then
    begin
      let tl' = prefix_base tl (length tl - 1) in
      prefix_verifiable_snoc tl;
      prefix_verifiable tl' i
    end

let prefix (tl: verifiable_log) (i: nat{i <= length tl})
  : verifiable_log
  = prefix_base tl i

let state_pre (tl: verifiable_log) (i: seq_index tl)
  : tsm: valid_tsm { let t,l = prefix tl i in
                     tsm.processed_entries == l /\
                     tsm.thread_id == t }
  = let tl': verifiable_log = prefix tl i in
    let tsm = state tl' in
    tsm

let state_post (tl: verifiable_log) (i: seq_index tl)
  : tsm: valid_tsm { let t,l = prefix tl (i+1) in
                     tsm.processed_entries == l /\
                     tsm.thread_id == t }
  = let tl' = prefix tl (i+1) in
    state tl'

let epoch_of (tl: verifiable_log) (i: seq_index tl)
  = let tl' = prefix tl (i+1) in
    let tsm' = state tl' in
    epoch_of_timestamp tsm'.clock

let lemma_state_transition (tl: verifiable_log) (i: seq_index tl)
  : Lemma (ensures (state_post tl i ==
                    verify_step_model (state_pre tl i) (index tl i)))
  = ()

(* the i'th entry is an appfn and the clock after processing it is <= ep *)
let is_appfn_within_epoch (ep: epoch_id) (tl: verifiable_log) (i: seq_index tl)
  = let i_ep = lift_epoch ep in
    let ep' = epoch_of tl i in
    let i_ep' = lift_epoch ep' in
    is_appfn tl i && i_ep' <= i_ep

#push-options "--fuel 1 --ifuel 1 --query_stats"

let lemma_valid_app_param (tl: verifiable_log) (i: seq_index tl { is_appfn tl i })
  : Lemma (ensures (let tsm = state_pre tl i in
                    let e = index tl i in
                    Zeta.Steel.AppSim.valid_runapp_param tsm e))
  = lemma_state_transition tl i

let to_app_fcr (tl: verifiable_log) (i: seq_index tl { is_appfn tl i })
  : GTot (appfn_call_res app)
  = let tsm = state_pre tl i in

    let open Zeta.Steel.AppSim in
    lemma_valid_app_param tl i;
    assert (valid_runapp_param tsm (index tl i));
    let (| f, a, r, o |) = runapp_output tsm (index tl i) in
    let open AS in
    { fid_cr = f ;
      arg_cr = a;
      inp_cr = r;
      res_cr = o;
    }

#pop-options

let rec app_fcrs (ep: TSM.epoch_id) (tl: verifiable_log)
  : GTot (Seq.seq (appfn_call_res app))
    (decreases (length tl))
  = if length tl = 0 then Seq.empty
    else
    begin
      let i = length tl - 1 in
      let tl' = prefix tl i in
      let fcrs' = app_fcrs ep tl' in
      if is_appfn_within_epoch ep tl i then
        SA.append1 fcrs' (to_app_fcr tl i)
      else
        fcrs'
    end

let app_fcrs_empty (ep: TSM.epoch_id) (tl: verifiable_log)
  : Lemma (ensures (length tl = 0 ==> app_fcrs ep tl == Seq.empty))
  = ()

let app_fcrs_snoc (ep: TSM.epoch_id) (tl: verifiable_log {length tl > 0})
  : Lemma (ensures (let i = length tl - 1 in
                    let _tl = prefix tl i in
                    let _fcrs = app_fcrs ep _tl in
                    let fcrs = app_fcrs ep tl in
                    if is_appfn_within_epoch ep tl i then
                      fcrs == SA.append1 _fcrs (to_app_fcr tl i)
                    else
                      fcrs == _fcrs))
  = ()

let lift_verifiable_log (tl: verifiable_log)
  : GTot i_verifiable_log
  = let tsm = to_tsm tl in
    to_ilog tsm

let lemma_lift_prefix_commute (tl: verifiable_log) (i:nat {i <= length tl})
  : Lemma (ensures (lift_verifiable_log (prefix tl i) == GT.prefix (lift_verifiable_log tl) i))
  = let (t,l) = tl in
    let (t,l') = prefix tl i in
    assert (l' == SA.prefix l i);

    let (i_t,i_l') = lift_verifiable_log (t,l') in
    assert (related_tid t i_t);

    let (_, i_l) = lift_verifiable_log tl in
    Zeta.Steel.LogRel.lift_prefix_commute l i

let pre_states_related (tl: verifiable_log) (i: seq_index tl)
  : Lemma (ensures (let i_tl = lift_verifiable_log tl in
                    let tsm = state_pre tl i in
                    let i_tsm = GT.state_pre i_tl i in
                    related_tsm tsm i_tsm))
  = lemma_lift_prefix_commute tl i

let post_states_related (tl: verifiable_log) (i: seq_index tl)
  : Lemma (ensures (let i_tl = lift_verifiable_log tl in
                    let tsm = state_post tl i in
                    let i_tsm = GT.state_post i_tl i in
                    related_tsm tsm i_tsm))
  = lemma_lift_prefix_commute tl (i+1)

let epoch_related (tl: verifiable_log) (i: seq_index tl)
  : Lemma (ensures (let i_tl = lift_verifiable_log tl in
                    let ep = epoch_of tl i in
                    let i_ep = GT.epoch_of i_tl i in
                    related_epoch ep i_ep))
  = let tl' = prefix tl (i+1) in
    let tsm' = to_tsm tl' in

    let i_tl = lift_verifiable_log tl in
    let i_tl' = GT.prefix i_tl (i+1) in
    lemma_lift_prefix_commute tl (i+1);
    let i_tsm' = GT.state i_tl' in

    assert (related_tsm tsm' i_tsm');
    assert (related_timestamp tsm'.clock i_tsm'.IV.clock);
    related_timestamp_epoch tsm'.clock i_tsm'.IV.clock;
    ()

let is_appfn_within_epoch_related
  (ep: TSM.epoch_id)
  (tl: verifiable_log)
  (i: seq_index tl)
  : Lemma (ensures (let i_tl = lift_verifiable_log tl in
                    let i_ep = lift_epoch ep in
                    is_appfn_within_epoch ep tl i = GT.is_appfn_within_epoch i_ep i_tl i))
  = epoch_related tl i

module GV = Zeta.GenericVerifier

let app_fcr_same
  (tl: verifiable_log)
  (i: seq_index tl {is_appfn tl i})
  : Lemma (ensures (let i_tl = lift_verifiable_log tl in
                    GT.is_appfn i_tl i /\
                    to_app_fcr tl i == GT.to_app_fcr i_tl i))
  = let open Zeta.Steel.AppSim in
    let s_fcr = to_app_fcr tl i in

    let tsm = state_pre tl i in
    let e = index tl i in
    lemma_valid_app_param tl i;
    assert (valid_runapp_param tsm e);
    assert (related_output (runapp_output tsm e) s_fcr);

    let i_tl = lift_verifiable_log tl in
    let i_fcr = GT.to_app_fcr i_tl i in
    let i_e = GT.index i_tl i in
    assert (related_log_entry e i_e);

    let i_tsm = GT.state_pre i_tl i in
    pre_states_related tl i;
    assert (related_tsm tsm i_tsm);

    let i_tsm_ = GT.state_post i_tl i in
    post_states_related tl i;
    assert (i_tsm_.IV.valid);
    GT.lemma_state_transition i_tl i;
    assert (i_tsm_ == GV.verify_step i_e i_tsm);
    assert (i_fcr == GV.appfn_result i_e i_tsm);

    runapp_output_related tsm i_tsm e i_e

let rec spec_rel_implies_same_fcrs (ep: TSM.epoch_id) (tl: verifiable_log)
  : Lemma (ensures (let s_fcrs = app_fcrs ep tl in
                    let tsm = to_tsm tl in
                    let tl = to_ilog tsm in
                    let i_ep = lift_epoch ep in
                    let i_fcrs = GT.app_fcrs_within_ep i_ep tl in
                    s_fcrs == i_fcrs))
          (decreases (length tl))
  = let i_tl = lift_verifiable_log tl in
    let i_ep = lift_epoch ep in
    let s_fcrs = app_fcrs ep tl in
    let i_fcrs = GT.app_fcrs_within_ep i_ep i_tl in
    if length tl = 0 then
    begin
      app_fcrs_empty ep tl;
      GT.app_fcrs_empty i_ep i_tl;
      Seq.lemma_empty i_fcrs
    end
    else
    begin
      let i = length tl - 1 in
      let _tl = prefix tl i in
      let _i_tl = lift_verifiable_log _tl in
      spec_rel_implies_same_fcrs ep _tl;
      lemma_lift_prefix_commute tl i;
      assert (_i_tl == GT.prefix i_tl i);
      app_fcrs_snoc ep tl;
      GT.app_fcrs_snoc i_ep i_tl;
      is_appfn_within_epoch_related ep tl i;
      if is_appfn_within_epoch ep tl i then
        app_fcr_same tl i
    end
