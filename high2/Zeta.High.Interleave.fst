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

let is_eac #app #n (il: verifiable_log app n)
  = is_eac_log (vlog_ext_of_il_log il)

let lemma_eac_empty #app #n (il: verifiable_log app n{S.length il = 0})
  : Lemma (ensures (is_eac il))
  = let le = vlog_ext_of_il_log il in
    eac_empty_log le

(* state after processing the i'th element *)
let eac_state_of_key (#app #n:_) (k: base_key)
  : IF.seqfn_t (gen_seq app n) (eac_state app k)
  = admit()

let empty_implies_eac (#app #n:_) (il: verifiable_log app n)
  : Lemma (ensures (length il = 0 ==> is_eac il))
  = if length il = 0 then
      let le = vlog_ext_of_il_log il in
      eac_empty_log le
    else ()

let eac_state_transition (#app #n:_) (k: base_key)
  (il: verifiable_log app n) (i: seq_index il)
  : Lemma (ensures (let es_pre = IF.to_pre_fn (eac_state_of_key k) il i in
                    let es_post = IF.to_post_fn (eac_state_of_key k) il i in
                    let smk = eac_smk app k in
                    let ee = mk_vlog_entry_ext il i in
                    es_post = eac_add ee es_pre))
  = admit()

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

let eac_implies_eac_state_valid (#app #n:_) (k: base_key)
  (il: verifiable_log app n)
  : Lemma (ensures (is_eac il ==> eac_state_of_key k il <> EACFail))
  = admit()

let eac_state_of_root_init (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (eac_state_of_key Zeta.BinTree.Root il = EACInit))
  = admit()

let eac_state_active_implies_prev_add (#app #n:_) (k: base_key) (il: eac_log app n)
  : Lemma (ensures (is_eac_state_active k il <==> has_some_add_of_key k il))
  = admit()

(* when the eac_state of k is instore, then k is in the store of a unique verifier thread *)
let stored_tid (#app:_) (#n:nat) (k: base_key) (il: eac_log app n {EACInStore? (eac_state_of_key k il)})
  : tid:nat{tid < n /\ store_contains (thread_store tid il) k}
  = admit()

let lemma_instore (#app #n:_) (bk: base_key) (il: eac_log app n)
  : Lemma (ensures (exists_in_some_store bk il <==> EACInStore? (eac_state_of_key bk il)))
  = admit()

(* uniqueness: k is never in two stores *)
let key_in_unique_store (#app #n:_) (k:base_key) (il: eac_log app n) (tid1 tid2: thread_id il)
  : Lemma (ensures (tid1 <> tid2 ==>
                    ~ (store_contains (thread_store tid1 il) k /\ store_contains (thread_store tid2 il) k)))
  = admit()

let to_gen_key (#app #n:_) (bk: base_key) (il: eac_log app n {is_eac_state_active bk il})
  : gk:key app {to_base_key gk = bk}
  = admit()

let stored_key_is_correct (#app #n:_) (bk: base_key) (il: eac_log app n{EACInStore? (eac_state_of_key bk il)})
  : Lemma (ensures (let tid = stored_tid bk il in
                    let st = thread_store tid il in
                    stored_key st bk = to_gen_key bk il))
  = admit()

let lemma_root_in_store0 (#app #n:_) (il: verifiable_log app n)
  : Lemma (requires (n > 0))
          (ensures (store_contains (thread_store 0 il) Zeta.BinTree.Root))
  = admit()

let lemma_root_not_in_store (#app #n:_) (tid: nat{tid < n /\ tid > 0}) (il: verifiable_log app n)
  : Lemma (not (store_contains (thread_store tid il) Zeta.BinTree.Root))
  = admit()

let eac_value (#app #n:_) (k: key app) (il: eac_log app n)
  : value_t k
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

let eac_fail_key (#app #n:_) (il: neac_log app n)
  : k:base_key {let i = eac_boundary il in
                IF.to_post_fn (eac_state_of_key k) il i = EACFail /\
                IF.to_pre_fn (eac_state_of_key k) il i <> EACFail}
  = admit()
