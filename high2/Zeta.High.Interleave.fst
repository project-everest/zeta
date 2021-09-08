module Zeta.High.Interleave

let mk_vlog_entry_ext #app #n (il: verifiable_log app n) (i: seq_index il)
  = let vle = I.index il i in
    let open Zeta.GenericVerifier in
    let open Zeta.High.Verifier in
    let vs = cur_thread_state_pre il i in
    lemma_cur_thread_state_extend il i;

    match vle with
    | EvictM k k' ->
      let v = stored_value vs.st k in
      EvictMerkle vle v
    | EvictB k ts ->
      let v = stored_value vs.st k in
      let tid = vs.tid in
      EvictBlum vle v tid
    | EvictBM k _ ts ->
      let v = stored_value vs.st k in
      let tid = vs.tid in
      EvictBlum vle v tid
    | RunApp f p ss ->
      assert(Some? (get_record_set ss vs));
      assert(SA.distinct_elems ss);
      let rs = get_record_set_succ ss vs in
      App vle rs
    | v -> NEvict v

let vlog_entry_ext_prop (#app #n:_) (il: verifiable_log app n) (i: seq_index il)
  : Lemma (ensures (let ee = mk_vlog_entry_ext il i in
                    let e = I.index il i in
                    e = to_vlog_entry ee))
  = ()

let is_eac_post (#app: app_params) (#n:nat)
  (il: verifiable_log app n) (i: seq_index il)
  : bool
  = let il' = prefix il (i+1) in
    let l' = vlog_ext_of_il_log il' in
    is_eac_log l'

let is_eac #app #n (il: verifiable_log app n)
  = is_eac_log (vlog_ext_of_il_log il)

let lemma_eac_empty #app #n (il: verifiable_log app n{S.length il = 0})
  : Lemma (ensures (is_eac il))
  = let le = vlog_ext_of_il_log il in
    eac_empty_log le

let lemma_eac_implies_prefix_eac (#app #n:_) (il: verifiable_log app n) (i: nat{i <= S.length il})
  : Lemma (ensures (is_eac il ==> is_eac (prefix il i)))
  = let open Zeta.IdxFn in
    if is_eac il then
      lemma_map_prefix mk_vlog_entry_ext il i
    else ()

let lemma_eac_implies_appfn_calls_seq_consistent (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (let gl = to_glog il in
                    Zeta.AppSimulate.seq_consistent (G.appfn_calls gl)))
  = admit()

let eac_boundary (#app #n:_) (il: neac_log app n)
  : (i: seq_index il{is_eac (prefix il i) /\
                     ~ (is_eac (prefix il (i+1)))})
  = let open Zeta.IdxFn in
    let le = vlog_ext_of_il_log il in
    let i = max_eac_prefix le in
    lemma_map_prefix mk_vlog_entry_ext il i;
    lemma_map_prefix mk_vlog_entry_ext il (i+1);
    i

let eac_boundary_not_appfn (#app #n:_) (il: neac_log app n)
  : Lemma (ensures (let i = eac_boundary il in
                    let e = I.index il i in
                    not (V.is_appfn e)))
  = let i = eac_boundary il in
    let e = I.index il i in
    let ee = mk_vlog_entry_ext il i in
    let le = vlog_ext_of_il_log il in
    let k = eac_fail_key le in
    let smk = eac_smk app k in
    let lei = SA.prefix le i in
    let lei' = SA.prefix le (i+1) in
    let open Zeta.SeqMachine in
    assert(valid smk lei);
    assert(~ (valid smk lei'));

    if V.is_appfn e then (
      admit()
    )
    else ()
