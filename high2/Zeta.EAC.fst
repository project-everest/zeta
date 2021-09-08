module Zeta.EAC

open Zeta.SeqMachine
open Zeta.SeqAux

let eac_state_of_base_key
  (#app: app_params)
  (k: base_key)
  (l: vlog_ext app)
  : eac_state app k
  = seq_machine_run (eac_smk app k) l

let eac_state_transition_aux
  (#app: app_params)
  (k: base_key)
  (l: vlog_ext app {length l > 0})
  : Lemma (ensures (let open Zeta.SeqAux in
                    let n = length l - 1 in
                    let l' = prefix l n in
                    let ee = index l n in
                    let es' = eac_state_of_base_key k l' in
                    let es = eac_state_of_base_key k l in
                    es = eac_add ee es'))
          [SMTPat (eac_state_of_base_key k l)]
  = let n = length l - 1 in
    let l' = prefix l n in
    let ee = index l n in
    let smk = eac_smk app k in
    lemma_hprefix_append_telem l;
    lemma_reduce_append (init_state smk) (trans_fn smk) l' ee

let eac_state_transition
  (#app: app_params)
  (k: key app)
  (l: vlog_ext app {length l > 0})
  : Lemma (ensures (let open Zeta.SeqAux in
                    let n = length l - 1 in
                    let l' = prefix l n in
                    let ee = index l n in
                    let es' = eac_state_of_key k l' in
                    let es = eac_state_of_key k l in
                    es = eac_add ee es'))
  = let bk = to_base_key k in
    eac_state_transition_aux bk l

let eac_empty_log
  (#app: app_params)
  (l: vlog_ext app {length l = 0})
  : Lemma (ensures (eac l))
          [SMTPat (eac l)]
  = lemma_empty l;
    let aux (k: base_key)
        : Lemma (ensures (valid (eac_smk app k) l))
                  [SMTPat (valid (eac_smk app k) l)]
      = lemma_empty_seq_valid (eac_smk app k)
    in
    ()

let rec search_keys_subtree (f: base_key -> bool) (k: base_key)
  : Tot (o: (option base_key)
    {
      o = None /\ (forall (k': base_key). Zeta.BinTree.is_desc k' k ==> f k')
        \/
      Some? o /\ not ( f (Some?.v o) )
    })
    (decreases (height k))
    = let open Zeta.BinTree in
      if not (f k) then Some k
      else if height k = 0 then (
        let aux (k':base_key)
          : Lemma (ensures (is_desc k' k ==> f k'))
          = if k' = k then ()
            else if not (is_desc k' k) then ()
            else assert(is_proper_desc k' k)
        in
        FStar.Classical.forall_intro aux;
        None
      )
      else
        let ol = search_keys_subtree f (LeftChild k) in
        let or = search_keys_subtree f (RightChild k) in
        if Some? ol then ol
        else if Some? or then or
        else (
          let aux (k': base_key)
            : Lemma (ensures (is_desc k' k ==> f k'))
            = if k' = k then ()
              else if not (is_desc k' k) then ()
              else
                let d = desc_dir k' k in
                if d = Left then ()
                else ()
          in
          FStar.Classical.forall_intro aux;
          None
        )

(* since the space of keys is finite, we can computationally determine if a property is true for all keys
 * or find a key if this is not the case *)
let search_keys (f: base_key -> bool)
  : o: (option base_key)
    {
      o = None /\ (forall (k: base_key). f k)
        \/
      Some? o /\ not (f (Some?.v o))
    }
  = let open Zeta.BinTree in
    let o = search_keys_subtree f Root in
    if None = o then (
      let aux (k: base_key)
        : Lemma (ensures (f k))
                [SMTPat (f k)]
        = lemma_root_is_univ_ancestor k
      in
      o
    )
    else o

let eac_induction_step_helper
  (#app: app_params)
  (l: vlog_ext app{let n = length l in n > 0 /\ eac (prefix l (n - 1))})
  : o: (option base_key)
    {let n = length l in
      o = None /\ eac l
          \/
          Some? o /\
          (let k = Some?.v o in
           eac_state_of_base_key k l = EACFail)
    }
  = let n = length l - 1 in
    let l' = prefix l n in
    let ee = index l n in
    let e = to_vlog_entry ee in
    let f = fun (k: base_key) -> valid (eac_smk app k) l in
    search_keys f

let rec max_eac_prefix_aux
  (#app: app_params)
  (l:vlog_ext app)
  : Tot (ki: (base_key & nat) {
      let k,i = ki in
      eac l /\ i = length l
          \/
      i < length l /\
      eac (prefix l i) /\
      ~ (eac (prefix l (i + 1))) /\
      ~ (valid (eac_smk app k) (prefix l (i + 1)))
      })
     (decreases (length l))
  = let n = length l in
    if n = 0 then (
      eac_empty_log l;
      Zeta.BinTree.Root (* the returned key is don't care for eac l *), 0
    )
    else
      let l' = prefix l (n - 1) in
      let k,i' = max_eac_prefix_aux l' in
      if i' = n - 1 then
        let o = eac_induction_step_helper l in
        if None = o
        then Zeta.BinTree.Root, n
        else (
          let k = Some?.v o in
          let smk = eac_smk app k in
          assert(~ (valid smk l));
          k,n-1
        )
      else k,i'

let rec eac_implies_prefix_eac
  (#app: app_params)
  (l: eac_log app)
  (i: nat {i <= length l})
  : Lemma (ensures (eac (prefix l i)))
          (decreases (length l))
  = if i = length l then ()
    else
      let n = length l - 1 in
      let l' = prefix l n in
      let k,i' = max_eac_prefix_aux l' in
      if i' = n
      then
        eac_implies_prefix_eac l' i
      else
        let smk = eac_smk app k in
        lemma_valid_prefix smk l (i' + 1)

let lemma_eac_state_of_key
  (#app: app_params)
  (l: eac_log app)
  (k: key app)
  : Lemma (ensures (eac_state_of_key k l <> EACFail))
  = let bk = to_base_key k in
    let smk = eac_smk app bk in
    assert(valid smk l);
    ()

let max_eac_prefix
  (#app: app_params)
  (l:vlog_ext app)
  : (i:nat{eac l /\ i = length l
          \/
          i < length l /\
          eac (prefix l i) /\
          ~ (eac (prefix l (i + 1)))})
  = let _,i = max_eac_prefix_aux l in
    i

let eac_fail_key
  (#app: app_params)
  (l:vlog_ext app {~ (eac l)})
  : k:base_key {let open Zeta.SeqAux in
                let i = max_eac_prefix l in
                ~ (valid (eac_smk app k) (prefix l (i+1)))}
  = let k,i = max_eac_prefix_aux l in
    k

(* computable version of eac *)
let is_eac_log (#app: app_params) (l:vlog_ext app): (r:bool{r <==> eac l})
  = let i = max_eac_prefix l in
    if i = length l
    then true
    else false

let eac_value_base (#app: app_params) (k: key app) (l: eac_log app)
  : value app
  = let es = eac_state_of_key k l in
    match es with
    | EACInit -> init_value k
    | EACInStore _ gk v -> if gk = k then v else init_value k
    | EACEvictedMerkle gk v -> if gk = k then v else init_value k
    | EACEvictedBlum gk v _ _ -> if gk = k then v else init_value k

let rec lemma_eac_value_compatible (#app: app_params) (k: key app) (l: eac_log app)
  : Lemma (ensures (Zeta.Record.compatible k (eac_value_base k l)))
          (decreases (length l))
          [SMTPat (eac_value_base k l)]
  = let n = length l in
    let bk = to_base_key k in
    let smk = eac_smk app bk in
    lemma_eac_state_of_key l k;
    if n = 0 then
      lemma_empty_seq_init smk l
    else (
      let l' = prefix l (n - 1) in
      let es' = eac_state_of_base_key bk l' in
      let ee = index l (n - 1) in
      let e = to_vlog_entry ee in
      lemma_eac_value_compatible k l';
      if not (e `refs_key` bk)
      then ()
      else
        match es' with
        | EACInit -> (
          match ee with
          | NEvict (AddM (k2,v) _ _) -> ()
          | _ -> ()
        )
        | _ -> ()
    )

let eac_value (#app: app_params) (k: key app) (l: eac_log app)
  : value_t k
  = eac_value_base k l

open Zeta.AppSimulate.Helper

let eac_valid_prop (#app: app_params) (l: eac_log app)
  = let fs = appfn_call_seq l in
    valid fs /\
    eac_app_state l == post_state fs

let eac_valid_helper_init #app (l: eac_log app{length l = 0})
  : Lemma (ensures (eac_valid_prop l))
  = let fs = appfn_call_seq l in
    lemma_valid_empty fs;
    assert(valid fs);

    let ste = eac_app_state l in
    let sta = post_state fs in
    let aux (ak: app_key app.adm)
      : Lemma (ensures (ste ak = sta ak))
      = lemma_init_value_null fs ak;
        let bk = to_base_key (AppK ak) in
        lemma_empty_seq_init (eac_smk app bk) l
    in
    FStar.Classical.forall_intro aux;
    assert(app_state_feq ste sta);
    ()

let appfn_call_seq_unchanged #app (l: eac_log app)
  : Lemma (requires (length l > 0 /\ not (App? (telem l))))
          (ensures (appfn_call_seq l == appfn_call_seq (hprefix l)))
  = ()

let appfn_call_seq_append #app (l: eac_log app)
  : Lemma (requires (length l > 0 /\ App? (telem l)))
          (ensures (let fc = to_fncall (telem l) in
          appfn_call_seq l == append1 (appfn_call_seq (hprefix l)) fc))
  = ()

let app_key_eac_value_unchanged_by_nonapp_entry #app (l: eac_log app) (gk: key app{AppK? gk})
  : Lemma (requires (length l > 0 /\ ~ (App? (telem l))))
          (ensures (let l' = hprefix l in
                    eac_value gk l = eac_value gk l'))
  = ()


let eac_refs_is_app_refs (#app: app_params) (l: eac_log app) (ak: app_key app.adm)
  : Lemma (requires (length l > 0 /\ App? (telem l)))
          (ensures (let gk = AppK ak in
                    let ee = telem l in
                    let App (RunApp _ _ refkeys) _ = ee in
                    let e = to_vlog_entry ee in
                    let bk = to_base_key gk in
                    let fc = to_fncall ee in

                    fc `refs` ak ==>
                    e `refs_key` bk /\ index_mem bk refkeys = refkey_idx fc ak))
  = let ee = telem l in
    let App (RunApp _ _ refkeys) rs = ee in
    let e = to_vlog_entry ee in
    let fc = to_fncall ee in

    if refs_comp fc ak then (
      let idx = refkey_idx fc ak in

      (* the base key at location idx *)
      let bk' = index refkeys idx in        // we don't know yet bk' = bk

      // clearly bk' is referenced by e
      assert(e `refs_key` bk');

      let l' = hprefix l in
      assert(eac l');

      let eac_smk = eac_smk app bk' in   // state machine for the leaf key
      assert(Zeta.SeqMachine.valid eac_smk l');         // running the state machine on l' results in valid state
      assert(Zeta.SeqMachine.valid eac_smk l);          // since (eac l)

      let es' = eac_state_of_base_key bk' l' in
      let es = eac_state_of_base_key bk' l in

      assert(es = eac_add ee es');      // es is obtained by running eac_add on ee and es'
      assert(es = eac_add_app ee es');  // .. since ee is App?
      assert(EACInStore? es');          // otherwise es should be EACFail
      match es' with
      | EACInStore _ gk _ ->
        assert(gk = AppK ak);           // we check this in eac_pp_add
        ()
    )
    else ()


let non_ref_key_eac_value_unchanged #app (l: eac_log app) (ak: app_key app.adm)
  : Lemma (requires (length l > 0 /\
                     (let ee = telem l in
                      let e = to_vlog_entry ee in
                      App? (telem l) /\ ~ ( (to_fncall ee) `refs` ak))))
          (ensures (let l' = hprefix l in
                    let gk = AppK ak in
                    eac_value gk l = eac_value gk l'))
  = let ee = telem l in
    let e = to_vlog_entry ee in
    let gk = AppK ak in
    let bk = to_base_key gk in
    let fc = to_fncall ee in
    let App (RunApp _ _ refkeys) rs = ee in

    if e `refs_key` bk then (
      let idx = index_mem bk refkeys in
      let l' = hprefix l in
      assert(eac l');

      let eac_smk = eac_smk app bk in   // state machine for the leaf key
      assert(Zeta.SeqMachine.valid eac_smk l');         // running the state machine on l' results in valid state
      assert(Zeta.SeqMachine.valid eac_smk l);          // since (eac l)

      let es' = eac_state_of_base_key bk l' in
      let es = eac_state_of_base_key bk l in

      assert(es = eac_add ee es');      // es is obtained by running eac_add on ee and es'
      assert(es = eac_add_app ee es');  // .. since ee is App?
      assert(EACInStore? es');          // otherwise es should be EACFail

      match es' with
      | EACInStore _ gk' v ->
        let ak',v' = index rs idx in
        assert(AppK ak' = gk');

        if ak' = ak then
          refs_witness fc ak idx
        else ()
    )
    else ()

let eac_implies_appfn_success (#app: app_params) (l: eac_log app)
  : Lemma (requires (length l > 0 /\ App? (telem l)))
          (ensures (correct (to_fncall (telem l))))
          [SMTPat (eac l)]
  = let ee = telem l in
    let e = to_vlog_entry ee in
    let fc = to_fncall ee in
    let l' = hprefix l in
    assert(eac l');

    // Root is any key
    let open Zeta.BinTree in
    let eac_smk = eac_smk app Root in
    assert(Zeta.SeqMachine.valid eac_smk l');
    assert(Zeta.SeqMachine.valid eac_smk l);          // since (eac l)
    let es' = eac_state_of_base_key Root l' in
    let es = eac_state_of_base_key Root l in

    assert(es = eac_add ee es');      // es is obtained by running eac_add on ee and es'
    assert(es = eac_add_app ee es');  // .. since ee is App?
    ()

let ref_key_value_change #app (l: eac_log app) (ak: app_key app.adm)
  : Lemma (requires (length l > 0 /\
                    (let k = AppK ak in
                     let ee = telem l in
                     let e = to_vlog_entry ee in
                     let bk = to_base_key k in
                     App? ee /\ (to_fncall ee) `refs` ak)))
          (ensures (let k = AppK ak in
                    let ee = telem l in
                    let fc = to_fncall ee in
                    eac_value k l = AppV (write fc ak)))
  = let ee = telem l in               // the tail element
    let gk = AppK ak in               // generalized key
    let bk = to_base_key gk in        // base-key
    assert(bk == app.keyhashfn ak);   // is simply a hash of app key to 256 bits

    let l' = hprefix l in
    assert(eac l');                   // eac l => eac (prefix l)

    let eac_smk = eac_smk app bk in   // state machine for the leaf key
    assert(Zeta.SeqMachine.valid eac_smk l');         // running the state machine on l' results in valid state
    assert(Zeta.SeqMachine.valid eac_smk l);          // since (eac l)

    let es' = eac_state_of_base_key bk l' in
    let es = eac_state_of_base_key bk l in

    assert(es = eac_add ee es');      // es is obtained by running eac_add on ee and es'
    assert(es = eac_add_app ee es');  // .. since ee is App?

    eac_refs_is_app_refs l ak;
    assert(EACInStore? es');          // otherwise, es would fail
    match ee with
    | App (RunApp f p refkeys) rs ->
      let fc = to_fncall ee in
      let idx = index_mem bk refkeys in
      assert(idx = refkey_idx fc ak);
      ()

let eac_valid_helper_nonapp (#app: app_params) (l: eac_log app)
  : Lemma (requires (length l > 0 /\
                     not (App? (telem l)) /\
                     eac_valid_prop (hprefix l)))
          (ensures (eac_valid_prop l))
  = appfn_call_seq_unchanged l;
    let fs = appfn_call_seq l in
    let app_state = post_state fs in
    let aux (k: app_key app.adm)
      : Lemma (ensures (let gk = AppK k in
                        eac_app_state l k = app_state k))
      = let gk = AppK k in
        app_key_eac_value_unchanged_by_nonapp_entry l gk
    in
    FStar.Classical.forall_intro aux;
    assert(app_state_feq app_state (eac_app_state l))

let eac_implies_input_consistent_key #app (l: eac_log app) (ak: app_key app.adm)
  : Lemma (requires (length l > 0 /\ App? (telem l) /\
                     to_fncall (telem l) `refs` ak))
          (ensures (let ee = telem l in
                    let fc = to_fncall ee in
                    let st = eac_app_state (hprefix l) in
                    refkey_inp_val fc ak = st ak))
  = //let ee = telem l in
    // let l' = hprefix l in
    // assert(eac l');

    // let fc = to_fncall ee in
    //let st = eac_app_state (hprefix l) in

    // the base-key of the application key ak
    let bk = to_base_key (AppK ak) in

    // deconstruct ee
    //match ee with
    //| App (RunApp f p refkeys) rs ->
      eac_refs_is_app_refs l ak;

      //let idx = index_mem bk refkeys in

      eac_state_transition_aux bk l;
      //let es = eac_state_of_base_key bk l in
      //let es' = eac_state_of_base_key bk l' in
      //assert(es = eac_add_app ee es');

      let eac_smk = eac_smk app bk in   // state machine for the leaf key
      //assert(valid eac_smk l');         // running the state machine on l' results in valid state
      assert(Zeta.SeqMachine.valid eac_smk l);          // since (eac l)

      //assert(EACInStore? es');          // otherwise, eac failure
      //match es' with
      //| EACInStore _ gk v ->
        // assert(gk = AppK ak);
        //assert(v = AppV (st ak));
        ()

let eac_implies_input_consistent #app (l: eac_log app)
  : Lemma (requires (length l > 0 /\ App? (telem l)))
          (ensures (let ee = telem l in
                    let fc = to_fncall ee in
                    let st = eac_app_state (hprefix l) in
                    input_consistent fc st))
          [SMTPat (eac l)]
  = let ee = telem l in
    let e = to_vlog_entry ee in
    let fc = to_fncall ee in
    let st = eac_app_state (hprefix l) in

    let aux (ak: app_key app.adm)
          : Lemma (ensures (fc `refs` ak ==> (refkey_inp_val fc ak = st ak)))
      = let bk = to_base_key (AppK ak) in
        eac_refs_is_app_refs l ak;
        if refs_comp fc ak then
          eac_implies_input_consistent_key l ak
        else ()
    in
    FStar.Classical.forall_intro aux;
    ()

let eac_valid_helper_app (#app: app_params) (l: eac_log app)
  : Lemma (requires (length l > 0 /\
                     App? (telem l) /\
                     eac_valid_prop (hprefix l)))
          (ensures (eac_valid_prop l))
  = let l' = hprefix l in
    let ee = telem l in
    let e = to_vlog_entry ee in

    (* the function call sequences of l' and l differ by the function call of the last element of l *)
    let fc = to_fncall ee in
    let fs = appfn_call_seq l in
    let fs' = appfn_call_seq l' in
    appfn_call_seq_append l;
    assert(fs == append1 fs' fc);

    (* since l is eac, every function call within l is "correct" - does not return failure *)
    assert(correct fc);

    (* from induction we know that simulating fs' succeeds and results in state st' (say) *)
    lemma_prefix1_append fs' fc;
    assert(hprefix fs == fs');
    let st' = post_state fs' in
    assert(st' == eac_app_state l');

    eac_implies_input_consistent l;
    correct_succeeds_if_input_consistent fc st';

    (* simulating fs does not fail *)
    assert(valid fs);

    (* final state after full simulation of fs is obtained by applying fc on st' *)
    let sts = post_state fs in
    assert(sts == apply_trans fc st');

    let ste = eac_app_state l in

    let aux (ak: app_key app.adm)
      : Lemma (ensures (sts ak = ste ak))
      = eac_refs_is_app_refs l ak;
        lemma_post_state fc st' ak;
        if refs_comp fc ak then
          ref_key_value_change l ak
        else
          non_ref_key_eac_value_unchanged l ak
    in
    FStar.Classical.forall_intro aux;
    assert(app_state_feq sts ste);
    ()

let rec eac_valid_helper (#app: app_params) (l: eac_log app)
  : Lemma (ensures eac_valid_prop l)
          (decreases (length l))
  = if (length l) = 0 then
       eac_valid_helper_init l
    else
      let i = length l - 1 in
      let l' = prefix l i in
      eac_valid_helper l';
      if App? (index l i) then
        eac_valid_helper_app l
      else
        eac_valid_helper_nonapp l

let eac_implies_valid_simulation (#app: app_params) (l: eac_log app)
  : Lemma (ensures (let fs = appfn_call_seq l in
                    Some? (simulate fs)))
  = eac_valid_helper l

let eac_state_is_app_state (#app: app_params) (l: eac_log app)
  : Lemma (ensures (let fs = appfn_call_seq l in
                    let app_state,_ = Some?.v (simulate fs) in
                    app_state == eac_app_state l))
  = eac_valid_helper l
