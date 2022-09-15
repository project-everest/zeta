module Zeta.Intermediate.Thread

open FStar.Classical

open Zeta.Ghost
open Zeta.BinTree
open Zeta.App
open Zeta.Key
open Zeta.Record
open Zeta.Intermediate.VerifierConfig
open Zeta.Intermediate.SlotKeyRel

module S = FStar.Seq
module SA = Zeta.SeqAux
module GV = Zeta.GenericVerifier

let ssm_feq (#vcfg:_) (ssm1 ssm2: slot_state_map vcfg)
  = forall s. ssm1 s = ssm2 s

let consistent_log (#vcfg:_) (tl: verifiable_log vcfg)
  = let t,l = tl in
    let st0 = init_store vcfg t in
    let s2k0 = Store.to_slot_state_map st0 in
    let st = store tl in
    let s2ks = Store.to_slot_state_map st in
    Logs.consistent_log s2k0 l /\
    (let s2kl = Logs.to_slot_state_map s2k0 l in
     ssm_feq s2ks s2kl)

let elim_consistent_log_slot (#vcfg:_) (tl: verifiable_log vcfg {consistent_log tl}) (s: slot_id vcfg)
  : Lemma (ensures (let t,l = tl in
                    let st0 = init_store vcfg t in
                    let s2k0 = Store.to_slot_state_map st0 in
                    slot_state_trans_closure s l (s2k0 s) <> None))
   = ()

let consistent_log_empty (#vcfg:_) (tl: verifiable_log vcfg)
  : Lemma (ensures (length tl = 0 ==> consistent_log tl))
  = if length tl = 0 then (
       let t,l = tl in
       let st0 = init_store vcfg t in
       let s2k0 = Store.to_slot_state_map st0 in
       let st = store tl in
       let s2ks = Store.to_slot_state_map st in

       let aux (s:_)
       : Lemma (ensures (slot_state_trans_closure s l (s2k0 s) <> None))
       = ()
       in
       forall_intro aux
    )

noeq type appfn_verify (vcfg: verifier_config) =
  | AFV: vs: vtls_t vcfg {vs.valid} ->
         e: logS_entry vcfg {GV.is_appfn e} -> appfn_verify vcfg

let app_pre_state (#vcfg:_) (a: appfn_verify vcfg)
  = a.vs

let app_post_state (#vcfg:_) (a: appfn_verify vcfg)
  = GV.verify_step a.e a.vs

let app_pre_store (#vcfg:_) (a: appfn_verify vcfg)
  = a.vs.st

let app_post_store (#vcfg:_) (a: appfn_verify vcfg)
  = let vs_ = app_post_state a in
    vs_.st

let appfn_verify_valid (#vcfg:_) (a: appfn_verify vcfg)
  = let vs_ = app_post_state a in
    vs_.valid

let appfn_slots (#vcfg:_) (a: appfn_verify vcfg)
  = let GV.RunApp _ _ ss = a.e in
    ss

let distinct_slots (#vcfg:_) (ss: S.seq (slot_id vcfg))
  = forall i1 i2. i1 <> i2 ==> S.index ss i1 <> S.index ss i2

let contains_distinct_app_keys (#vcfg:_) (a: appfn_verify vcfg)
  : GTot bool
  = GV.contains_distinct_app_keys_comp (app_pre_state a) (appfn_slots a)

let lemma_contains_only_app_keys (#vcfg:_) (a: appfn_verify vcfg)
  : Lemma (ensures (contains_distinct_app_keys a ==> contains_only_app_keys (app_pre_store a) (appfn_slots a)))
  = ()

let lemma_valid_implies_contains_distinct (#vcfg:_) (a: appfn_verify vcfg)
  : Lemma (ensures (appfn_verify_valid a ==> contains_distinct_app_keys a))
  = ()

let lemma_store_contains_ref_slots (#vcfg:_) (a: appfn_verify vcfg {appfn_verify_valid a}) (s: slot_id vcfg)
  : Lemma (requires (let ss = appfn_slots a in
                     S.mem s ss))
          (ensures (let st = app_pre_store a in
                    inuse_slot st s))
  = let st = app_pre_store a in
    let ss = appfn_slots a in

    lemma_valid_implies_contains_distinct a;
    lemma_contains_only_app_keys a;
    assert(contains_only_app_keys st ss);
    let i = S.index_mem s ss in
    eliminate forall i. contains_app_key st (S.index ss i) with i

let appfn_slots_distinct (#vcfg:_) (a: appfn_verify vcfg {contains_distinct_app_keys a})
  : Lemma (ensures (distinct_slots (appfn_slots a)))
  = let ss = appfn_slots a in
    let aux (i1 i2:_)
      : Lemma (i1 <> i2 ==> S.index ss i1 <> S.index ss i2)
      = if i1 <> i2 then (
          ()
        )
    in
    forall_intro_2 aux

let reads (#vcfg:_) (a: appfn_verify vcfg {contains_distinct_app_keys a})
  : GTot (S.seq (app_record vcfg.app.adm))
  = let intspec = int_verifier_spec vcfg in
    GV.reads #intspec (app_pre_state a) (appfn_slots a)

let appfn_succ (#vcfg:_) (a: appfn_verify vcfg)
  : GTot bool
  = let GV.RunApp f p _ = a.e in
    let ss = appfn_slots a in
    contains_distinct_app_keys a &&
    S.length ss = appfn_arity f &&
    (let rs = reads a in
     let fn = appfn f in
     let rc,_,_ = fn p rs in
     rc = Fn_success
    )

let writes (#vcfg:_) (a: appfn_verify vcfg {appfn_succ a})
  : GTot (ws:S.seq (app_value_nullable vcfg.app.adm){S.length ws = S.length (appfn_slots a)})
  = let GV.RunApp f p _ = a.e in
    let ss = appfn_slots a in
    let rs = reads a in
    let fn = appfn f in
    let _,_,ws = fn p rs in
    ws

let lemma_valid_implies_succ (#vcfg:_) (a: appfn_verify vcfg {appfn_verify_valid a})
  : Lemma (ensures (appfn_succ a))
  = let vs' = app_pre_state a in
    let vs = app_post_state a in
    let e = a.e in
    let GV.RunApp f p ss = a.e in

    assert(vs == GV.verify_step e vs');
    assert(ss == appfn_slots a);
    assert (contains_distinct_app_keys a);
    assert (S.length ss = appfn_arity f);
    let rs = reads a in
    assert (rs == GV.reads vs' ss);
    let fn = appfn f in
    let rc,_,_ = fn p rs in
    assert (rc <> Fn_failure);
    ()

let lemma_store_contains_unchanged (#vcfg:_) (a: _ {appfn_verify_valid a}) (s: slot_id vcfg)
  : Lemma (ensures (let st' = app_pre_store a in
                    let st = app_post_store a in
                    inuse_slot st s = inuse_slot st' s /\
                    (inuse_slot st' s ==>
                     stored_base_key st' s = stored_base_key st s /\
                     points_to_info st' s Left = points_to_info st s Left /\
                     points_to_info st' s Right = points_to_info st s Right)))
  = let st' = app_pre_store a in
    let ss = appfn_slots a in
    let rs = reads a in
    lemma_valid_implies_succ a;
    let ws = writes a in
    let st = app_post_store a in
    assert (st == puts_store st' ss ws);
    puts_preserves st' ss ws s;
    ()

#push-options "--fuel 1 --ifuel 1 --query_stats"

let consistent_log_snoc_appfn (#vcfg:_) (tl: verifiable_log vcfg {length tl > 0})
  : Lemma (requires (let i = length tl - 1 in
                     let tl' = prefix tl i in
                     let e = index tl i in
                     consistent_log tl' /\
                     GV.RunApp? e))
          (ensures (consistent_log tl))
  = let t,l = tl in
    let st0 = init_store vcfg t in
    let s2k0 = Store.to_slot_state_map st0 in

    let vs = state tl in
    let st = vs.st in
    let s2ks = Store.to_slot_state_map st in

    let i = length tl - 1 in
    let tl' = prefix tl i in
    let _,l' = tl' in
    let vs' = state tl' in
    let st' = vs'.st in
    let s2ks' = Store.to_slot_state_map st' in
    let s2kl' = Logs.to_slot_state_map s2k0 l' in
    assert(ssm_feq s2kl' s2ks');

    let e = index tl i in
    let GV.RunApp f p ss = e in

    lemma_state_transition tl i;
    assert(vs == GV.verify_step e vs');
    let a = AFV vs' e in

    let aux (s:_)
      : Lemma (ensures (slot_state_trans_closure s l (s2k0 s) <> None))
      = let sls' = slot_state_trans_closure s l' (s2k0 s) in

        elim_consistent_log_slot tl' s;
        assert(sls' <> None);

        eliminate forall s. s2ks' s = s2kl' s with s;
        assert(s2ks' s = s2kl' s);

        if S.mem s ss then
          lemma_store_contains_ref_slots a s
    in
    forall_intro aux;
    assert(Logs.consistent_log s2k0 l);
    let s2kl = Logs.to_slot_state_map s2k0 l in
    let aux (si:_)
      : Lemma (ensures (s2ks si = s2kl si))
      = lemma_store_contains_unchanged a si
    in
    forall_intro aux

#pop-options

#push-options "--fuel 1 --ifuel 1 --query_stats"

let consistent_log_snoc_addm (#vcfg:_) (tl: verifiable_log vcfg {length tl > 0})
  : Lemma (requires (let i = length tl - 1 in
                     let tl' = prefix tl i in
                     let e = index tl i in
                     consistent_log tl' /\
                     GV.AddM? e))
          (ensures (consistent_log tl))
  = let t,l = tl in
    let st0 = init_store vcfg t in
    let s2k0 = Store.to_slot_state_map st0 in

    let vs = state tl in
    let st = vs.st in
    let s2ks = Store.to_slot_state_map st in

    let i = length tl - 1 in
    let tl' = prefix tl i in
    let _,l' = tl' in
    let vs' = state tl' in
    let st' = vs'.st in
    let s2ks' = Store.to_slot_state_map st' in
    let s2kl' = Logs.to_slot_state_map s2k0 l' in
    assert(ssm_feq s2kl' s2ks');

    let e = index tl i in
    let GV.AddM r s s' = e in

    lemma_state_transition tl i;
    assert(vs == GV.verify_step e vs');

    assert(has_distinct_slots e);

    let aux (si:_)
      : Lemma (ensures (slot_state_trans_closure si l (s2k0 si) <> None))
      = let sls' = slot_state_trans_closure si l' (s2k0 si) in

        elim_consistent_log_slot tl' si;
        assert(sls' <> None);

        eliminate forall s. s2ks' s = s2kl' s with si;
        assert(s2ks' si = s2kl' si);

        ()
    in
    forall_intro aux;
    assert(Logs.consistent_log s2k0 l);
    let s2kl = Logs.to_slot_state_map s2k0 l in

    let aux (si:_)
      : Lemma (ensures (s2ks si = s2kl si))
      = ()
    in
    forall_intro aux

let consistent_log_snoc_addb (#vcfg:_) (tl: verifiable_log vcfg {length tl > 0})
  : Lemma (requires (let i = length tl - 1 in
                     let tl' = prefix tl i in
                     let e = index tl i in
                     consistent_log tl' /\
                     GV.AddB? e))
          (ensures (consistent_log tl))
  = let t,l = tl in
    let st0 = init_store vcfg t in
    let s2k0 = Store.to_slot_state_map st0 in

    let vs = state tl in
    let st = vs.st in
    let s2ks = Store.to_slot_state_map st in

    let i = length tl - 1 in
    let tl' = prefix tl i in
    let _,l' = tl' in
    let vs' = state tl' in
    let st' = vs'.st in
    let s2ks' = Store.to_slot_state_map st' in
    let s2kl' = Logs.to_slot_state_map s2k0 l' in
    assert(ssm_feq s2kl' s2ks');

    let e = index tl i in
    let GV.AddB r s _ _ = e in

    lemma_state_transition tl i;
    assert(vs == GV.verify_step e vs');

    assert(has_distinct_slots e);
    let aux (si:_)
      : Lemma (ensures (slot_state_trans_closure si l (s2k0 si) <> None))
      = let sls' = slot_state_trans_closure si l' (s2k0 si) in

        elim_consistent_log_slot tl' si;
        assert(sls' <> None);

        eliminate forall s. s2ks' s = s2kl' s with si;
        assert(s2ks' si = s2kl' si);

        ()
    in
    forall_intro aux;
    assert(Logs.consistent_log s2k0 l);
    let s2kl = Logs.to_slot_state_map s2k0 l in
    let s2kl = Logs.to_slot_state_map s2k0 l in

    let aux (si:_)
      : Lemma (ensures (s2ks si = s2kl si))
      = ()
    in
    forall_intro aux

let consistent_log_snoc_evictm (#vcfg:_) (tl: verifiable_log vcfg {length tl > 0})
  : Lemma (requires (let i = length tl - 1 in
                     let tl' = prefix tl i in
                     let e = index tl i in
                     consistent_log tl' /\
                     GV.EvictM? e))
          (ensures (consistent_log tl))
  = let t,l = tl in
    let st0 = init_store vcfg t in
    let s2k0 = Store.to_slot_state_map st0 in

    let vs = state tl in
    let st = vs.st in
    let s2ks = Store.to_slot_state_map st in

    let i = length tl - 1 in
    let tl' = prefix tl i in
    let _,l' = tl' in
    let vs' = state tl' in
    let st' = vs'.st in
    let s2ks' = Store.to_slot_state_map st' in
    let s2kl' = Logs.to_slot_state_map s2k0 l' in
    assert(ssm_feq s2kl' s2ks');

    let e = index tl i in
    let GV.EvictM s s' = e in

    lemma_state_transition tl i;
    assert(vs == GV.verify_step e vs');

    let aux (si:_)
      : Lemma (ensures (slot_state_trans_closure si l (s2k0 si) <> None))
      = let sls' = slot_state_trans_closure si l' (s2k0 si) in

        elim_consistent_log_slot tl' si;
        assert(sls' <> None);

        eliminate forall s. s2ks' s = s2kl' s with si;
        assert(s2ks' si = s2kl' si);

        ()
    in
    forall_intro aux;
    assert(Logs.consistent_log s2k0 l);
    let s2kl = Logs.to_slot_state_map s2k0 l in
    let aux (si:_)
      : Lemma (ensures (s2ks si = s2kl si))
      = ()
    in
    forall_intro aux

let consistent_log_snoc_evictb (#vcfg:_) (tl: verifiable_log vcfg {length tl > 0})
  : Lemma (requires (let i = length tl - 1 in
                     let tl' = prefix tl i in
                     let e = index tl i in
                     consistent_log tl' /\
                     GV.EvictB? e))
          (ensures (consistent_log tl))
  = let t,l = tl in
    let st0 = init_store vcfg t in
    let s2k0 = Store.to_slot_state_map st0 in

    let vs = state tl in
    let st = vs.st in
    let s2ks = Store.to_slot_state_map st in

    let i = length tl - 1 in
    let tl' = prefix tl i in
    let _,l' = tl' in
    let vs' = state tl' in
    let st' = vs'.st in
    let s2ks' = Store.to_slot_state_map st' in
    let s2kl' = Logs.to_slot_state_map s2k0 l' in
    assert(ssm_feq s2kl' s2ks');

    let e = index tl i in
    let GV.EvictB s t = e in

    lemma_state_transition tl i;
    assert(vs == GV.verify_step e vs');

    let aux (si:_)
      : Lemma (ensures (slot_state_trans_closure si l (s2k0 si) <> None))
      = let sls' = slot_state_trans_closure si l' (s2k0 si) in

        elim_consistent_log_slot tl' si;
        assert(sls' <> None);

        eliminate forall s. s2ks' s = s2kl' s with si;
        assert(s2ks' si = s2kl' si);

        ()
    in
    forall_intro aux;
    assert(Logs.consistent_log s2k0 l);
    let s2kl = Logs.to_slot_state_map s2k0 l in
    let aux (si:_)
      : Lemma (ensures (s2ks si = s2kl si))
      = if si = s then (
          assert(empty_slot st s);
          assert(s2ks s = Free);
          assert(s2kl s = Free);
          ()
        )
        else (
          assert(identical_except st st' s);
          ()
        )

    in
    forall_intro aux

#pop-options

#push-options "--z3rlimit_factor 3"

let consistent_log_snoc_evictbm (#vcfg:_) (tl: verifiable_log vcfg {length tl > 0})
  : Lemma (requires (let i = length tl - 1 in
                     let tl' = prefix tl i in
                     let e = index tl i in
                     consistent_log tl' /\
                     GV.EvictBM? e))
          (ensures (consistent_log tl))
  = let t,l = tl in
    let st0 = init_store vcfg t in
    let s2k0 = Store.to_slot_state_map st0 in

    let vs = state tl in
    let st = vs.st in
    let s2ks = Store.to_slot_state_map st in

    let i = length tl - 1 in
    let tl' = prefix tl i in
    let _,l' = tl' in
    let vs' = state tl' in
    let st' = vs'.st in
    let s2ks' = Store.to_slot_state_map st' in
    let s2kl' = Logs.to_slot_state_map s2k0 l' in
    assert(ssm_feq s2kl' s2ks');

    let e = index tl i in
    let GV.EvictBM s s' t = e in

    lemma_state_transition tl i;
    assert(vs == GV.verify_step e vs');
    assert(vs == evictbm s s' t vs');

    let aux (si:_)
      : Lemma (ensures (slot_state_trans_closure si l (s2k0 si) <> None))
      = let sls' = slot_state_trans_closure si l' (s2k0 si) in

        elim_consistent_log_slot tl' si;
        assert(sls' <> None);

        eliminate forall s. s2ks' s = s2kl' s with si;
        assert(s2ks' si = s2kl' si);

        ()
    in
    forall_intro aux;
    assert(Logs.consistent_log s2k0 l);
    let s2kl = Logs.to_slot_state_map s2k0 l in

    let aux (si:_)
      : Lemma (ensures (s2ks si = s2kl si))
      = if si = s then (
          assert(empty_slot st s);
          assert(s2ks si = Free);
          assert(s2kl si = Free);
          ()
        )
        else if si = s' then (
          assert(s2kl s' = s2kl' s');
          assert(inuse_slot st' s');
          assert(inuse_slot st s');
          assert(s2ks s' = s2ks' s');
          ()
        )
        else
          ()
    in
    forall_intro aux

#pop-options

let consistent_log_snoc_next_verify_epoch (#vcfg:_) (tl: verifiable_log vcfg {length tl > 0})
  : Lemma (requires (let i = length tl - 1 in
                     let tl' = prefix tl i in
                     let e = index tl i in
                     consistent_log tl' /\
                     (GV.NextEpoch? e \/ GV.VerifyEpoch? e)))
          (ensures (consistent_log tl))
  = let t,l = tl in
    let st0 = init_store vcfg t in
    let s2k0 = Store.to_slot_state_map st0 in

    let vs = state tl in
    let st = vs.st in
    let s2ks = Store.to_slot_state_map st in

    let i = length tl - 1 in
    let tl' = prefix tl i in
    let _,l' = tl' in
    let vs' = state tl' in
    let st' = vs'.st in
    let s2ks' = Store.to_slot_state_map st' in
    let s2kl' = Logs.to_slot_state_map s2k0 l' in
    assert(ssm_feq s2kl' s2ks');

    let e = index tl i in
    lemma_state_transition tl i;
    assert(vs == GV.verify_step e vs');
    let aux (si:_)
      : Lemma (ensures (slot_state_trans_closure si l (s2k0 si) <> None))
      = let sls' = slot_state_trans_closure si l' (s2k0 si) in

        elim_consistent_log_slot tl' si;
        assert(sls' <> None);

        eliminate forall s. s2ks' s = s2kl' s with si;
        assert(s2ks' si = s2kl' si);

        ()
    in
    forall_intro aux;
    assert(Logs.consistent_log s2k0 l);
    let s2kl = Logs.to_slot_state_map s2k0 l in
    let aux (si:_)
      : Lemma (ensures (s2ks si = s2kl si))
      = ()
    in
    forall_intro aux

#push-options "--fuel 0 --ifuel 1 --query_stats"
let consistent_log_snoc (#vcfg:_) (tl: verifiable_log vcfg {length tl > 0})
  : Lemma (requires (let i = length tl - 1 in
                     let tl' = prefix tl i in
                     let e = index tl i in
                     consistent_log tl'))
          (ensures (consistent_log tl))
  = let i = length tl - 1 in
    let tl' = prefix tl i in
    let e = index tl i in
    let open Zeta.GenericVerifier in

    match e with
    | AddM _ _ _ -> consistent_log_snoc_addm tl
    | AddB _ _ _ _ -> consistent_log_snoc_addb tl
    | EvictM _ _ -> consistent_log_snoc_evictm tl
    | EvictB _ _ -> consistent_log_snoc_evictb tl
    | EvictBM _ _ _ -> consistent_log_snoc_evictbm tl
    | RunApp _ _ _ -> consistent_log_snoc_appfn tl
    | _ -> consistent_log_snoc_next_verify_epoch tl

#pop-options

let rec lemma_consistent_log (#vcfg:_) (tl: verifiable_log vcfg)
  : Lemma (ensures (consistent_log tl))
          (decreases (length tl))
  = if length tl = 0 then
      consistent_log_empty tl
    else (
      let i = length tl - 1 in
      let tl' = prefix tl i in
      lemma_consistent_log tl';
      consistent_log_snoc tl
    )

let verifiable_implies_valid_log_entry
  (#vcfg:_)
  (tl: verifiable_log vcfg)
  (i: seq_index tl)
  : Lemma (ensures (let st = store_pre tl i in
                    let e = index tl i in
                    let s2k = Store.to_slot_state_map st in
                    Logs.valid_logS_entry s2k e))
  = let _tl = prefix tl i in
    let t,_l = _tl in
    let t, l = tl in
    let _st = store_pre tl i in

    let st0 = init_store vcfg t in
    let s2k0 = Store.to_slot_state_map st0 in

    lemma_consistent_log _tl;
    lemma_consistent_log tl;

    let e = index tl i in
    lemma_all_entries_valid s2k0 l i;
    let s2kl = Logs.to_slot_state_map s2k0 (SA.prefix l i) in
    assert(Logs.valid_logS_entry s2kl e);

    let s2ks = Store.to_slot_state_map _st in
    assert(ssm_feq s2kl s2ks);

    assert(Logs.valid_logS_entry s2ks e);

    ()

let sp_is_mp (#vcfg:_) (tl: verifiable_log vcfg)
  = let st = store tl in
    slot_points_to_is_merkle_points_to st

let sp_is_mp_empty (#vcfg:_) (tl: verifiable_log vcfg)
  : Lemma (ensures (length tl = 0 ==> sp_is_mp tl))
  = ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit_factor 4"

let sp_is_mp_snoc_addm (#vcfg:_) (tl: verifiable_log vcfg {length tl > 0})
  : Lemma (requires (let i = length tl - 1 in
                     let tl' = prefix tl i in
                     let e = index tl i in
                     sp_is_mp tl' /\
                     GV.AddM? e))
          (ensures (sp_is_mp tl))
  = let i = length tl - 1 in
    let vs1 = state tl in
    let st1 = vs1.st in

    let tl' = prefix tl i in
    let vs = state tl' in
    let st = vs.st in

    let e = index tl i in
    let GV.AddM r s s' = e in
    let a = AMP s r s' vs in
    lemma_state_transition tl i;
    assert(vs1 == GV.verify_step e vs);

    let aux (s1 s2 dx:_)
      : Lemma (ensures (slot_points_to_is_merkle_points_to_local st1 s1 s2 dx))
      = assert(slot_points_to_is_merkle_points_to_local st s1 s2 dx);
        if points_to_dir st1 s1 dx s2 then (
          if s1 = s then (
            assert(points_to_dir st s' (addm_dir a) s2);
            assert(slot_points_to_is_merkle_points_to_local st (addm_anc_slot a) s2 (addm_dir a));
            assert(s2 <> s);
            assert(s2 <> s');
            lemma_addm_identical_except2 vs e s2
          )
          else if s1 = s' then (
            if s2 = s then (
              let mv1' = to_merkle_value (stored_value st1 s') in
              let d = addm_dir a in
              assert(addm_anc_val_postcond a mv1');

              if d = dx then ()
              else (
                // let mv' = to_merkle_value (stored_value st s') in
                // assert(desc_hash_dir mv1' dx = desc_hash_dir mv' dx);
                assert(addm_anc_slot_points_postcond a st1);
                assert(points_to_info st1 s' dx = points_to_info st s' dx);
                assert(points_to_dir st1 s' dx s2);
                assert(points_to_dir st s' dx s2);
                ()
              )
            )
            else (
              assert(s2 <> s);
              if s2 = s' then (
                assert(slot_points_to_is_merkle_points_to_local st s' s' dx);
                ()
              )
              else (
                lemma_addm_identical_except2 vs e s2;
                assert(addm_anc_slot_points_postcond a st1);
                assert(dx = other_dir (addm_dir a));
                assert(s1 = addm_anc_slot a);
                assert(points_to_info st1 s' dx = points_to_info st s' dx);
                assert(points_to_dir st s' dx s2);
                assert(stored_key st s' = stored_key st1 s');
                ()
              )
            )
          )
          else (
            lemma_addm_identical_except2 vs e s1;
            assert(inuse_slot st s1);
            assert(inuse_slot st1 s1);
            assert(stored_value st1 s1 = stored_value st s1);
            ()
          )
        )
    in
    forall_intro_3 aux

#pop-options

#push-options "--fuel 0 --ifuel 1 --query_stats"

let sp_is_mp_snoc_addb (#vcfg:_) (tl: verifiable_log vcfg {length tl > 0})
  : Lemma (requires (let i = length tl - 1 in
                     let tl' = prefix tl i in
                     let e = index tl i in
                     sp_is_mp tl' /\
                     GV.AddB? e))
          (ensures (sp_is_mp tl))
  = let i = length tl - 1 in
    let vs1 = state tl in
    let st1 = vs1.st in

    let tl' = prefix tl i in
    let vs = state tl' in
    let st = vs.st in

    let e = index tl i in
    let GV.AddB r s t j = e in

    lemma_state_transition tl i;
    assert(vs1 == GV.verify_step e vs);

    let aux (s1 s2: slot_id _) (dx: bin_tree_dir):
      Lemma (slot_points_to_is_merkle_points_to_local st1 s1 s2 dx) =
      if not (points_to_dir st1 s1 dx s2) then ()
      else (
        (* s points to nothing after addb *)
        assert(s1 <> s);
        assert(get_slot st s1 = get_slot st1 s1);
        assert(slot_points_to_is_merkle_points_to_local st s1 s2 dx);
        assert(points_to_dir st s1 dx s2);
        ()
      )
    in
    forall_intro_3 aux;
    ()

let sp_is_mp_snoc_evictb (#vcfg:_) (tl: verifiable_log vcfg {length tl > 0})
  : Lemma (requires (let i = length tl - 1 in
                     let tl' = prefix tl i in
                     let e = index tl i in
                     sp_is_mp tl' /\
                     GV.EvictB? e))
          (ensures (sp_is_mp tl))
  = let i = length tl - 1 in
    let vs1 = state tl in
    let st1 = vs1.st in

    let tl' = prefix tl i in
    let vs = state tl' in
    let st = vs.st in

    let e = index tl i in
    let GV.EvictB s t = e in

    lemma_state_transition tl i;
    assert(vs1 == GV.verify_step e vs);
    let aux (s1 s2: slot_id _) (dx: bin_tree_dir):
      Lemma (slot_points_to_is_merkle_points_to_local st1 s1 s2 dx) =

      if not (points_to_dir st1 s1 dx s2) then ()
      else (
        assert(s <> s1);
        assert(get_slot st s1 = get_slot st1 s1);
        assert(slot_points_to_is_merkle_points_to_local st s1 s2 dx);
        assert(points_to_dir st s1 dx s2);
        ()
      )
    in
    forall_intro_3 aux


let sp_is_mp_snoc_evictm (#vcfg:_) (tl: verifiable_log vcfg {length tl > 0})
  : Lemma (requires (let i = length tl - 1 in
                     let tl' = prefix tl i in
                     let e = index tl i in
                     sp_is_mp tl' /\
                     GV.EvictM? e))
          (ensures (sp_is_mp tl))
  = let i = length tl - 1 in
    let vs1 = state tl in
    let st1 = vs1.st in

    let tl' = prefix tl i in
    let vs = state tl' in
    let st = vs.st in

    let e = index tl i in
    let GV.EvictM s s' = e in

    lemma_state_transition tl i;
    assert(vs1 == GV.verify_step e vs);
    assert(empty_slot st1 s);
    assert(identical_except2 st st1 s s');
    let k = stored_base_key st s in
    let k' = stored_base_key st s' in
    assert(is_proper_desc k k');
    let d = desc_dir k k' in

    let aux (s1 s2: slot_id _) (dx: bin_tree_dir):
      Lemma (slot_points_to_is_merkle_points_to_local st1 s1 s2 dx) =
      if not (points_to_dir st1 s1 dx s2) then ()
      else (
        assert(s1 <> s);

        if s1 = s' then (
          assert(dx = other_dir d);
          assert(points_to_info st s' dx = points_to_info st1 s' dx);
          assert(slot_points_to_is_merkle_points_to_local st s1 s2 dx);
          ()
        )
        else (
          assert(get_slot st s1 = get_slot st1 s1);
          assert(points_to_dir st s1 dx s2);
          assert(slot_points_to_is_merkle_points_to_local st s1 s2 dx);
          ()
        )
      )
    in
    forall_intro_3 aux;
    ()

let sp_is_mp_snoc_evictbm (#vcfg:_) (tl: verifiable_log vcfg {length tl > 0})
  : Lemma (requires (let i = length tl - 1 in
                     let tl' = prefix tl i in
                     let e = index tl i in
                     sp_is_mp tl' /\
                     GV.EvictBM? e))
          (ensures (sp_is_mp tl))
  = let i = length tl - 1 in
    let vs1 = state tl in
    let st1 = vs1.st in

    let tl' = prefix tl i in
    let vs = state tl' in
    let st = vs.st in

    let e = index tl i in
    let GV.EvictBM s s' _ = e in
    lemma_state_transition tl i;
    assert(vs1 == GV.verify_step e vs);
    assert(identical_except2 st1 st s s');
    let k = stored_base_key st s in
    let k' = stored_base_key st s' in
    assert(is_proper_desc k k');
    let d = desc_dir k k' in

    let aux (s1 s2: slot_id _) (dx: bin_tree_dir):
      Lemma (slot_points_to_is_merkle_points_to_local st1 s1 s2 dx) =

      if not (points_to_dir st1 s1 dx s2) then ()
      else (
        assert(s <> s1);
        if s1 = s' then (
          assert(dx = other_dir d);
          assert(points_to_info st s' dx = points_to_info st1 s' dx);
          assert(slot_points_to_is_merkle_points_to_local st s1 s2 dx);
          ()
        )
        else (
          assert(get_slot st s1 = get_slot st1 s1);
          assert(slot_points_to_is_merkle_points_to_local st s1 s2 dx);
          assert(points_to_dir st s1 dx s2);
          ()
        )
      )
    in
    forall_intro_3 aux

#pop-options


#push-options "--fuel 1 --ifuel 1 --query_stats"

let sp_is_mp_snoc_appfn (#vcfg:_) (tl: verifiable_log vcfg {length tl > 0})
  : Lemma (requires (let i = length tl - 1 in
                     let tl' = prefix tl i in
                     let e = index tl i in
                     sp_is_mp tl' /\
                     GV.RunApp? e))
          (ensures (sp_is_mp tl))
  = let i = length tl - 1 in
    let vs1 = state tl in
    let st1 = vs1.st in

    let tl' = prefix tl i in
    let vs = state tl' in
    let st = vs.st in

    let e = index tl i in
    let a = AFV vs e in
    assert(appfn_verify_valid a);
    lemma_valid_implies_contains_distinct a;
    lemma_contains_only_app_keys a;
    let ss = appfn_slots a in
    lemma_valid_implies_succ a;
    let ws = writes a in
    assert (st1 == puts_store st ss ws);

    let aux (s1 s2: slot_id _) (dx: bin_tree_dir):
      Lemma (ensures (slot_points_to_is_merkle_points_to_local st1 s1 s2 dx))
      = lemma_store_contains_unchanged a s1;
        lemma_store_contains_unchanged a s2;
        assert(slot_points_to_is_merkle_points_to_local st s1 s2 dx);
        if points_to_dir st1 s1 dx s2 then (
          assert(points_to_dir st s1 dx s2);
          let k1 = stored_base_key st1 s1 in
          assert(k1 = stored_base_key st s1);
          assert(is_merkle_key k1);
          if S.mem s1 ss then (
            let i1 = S.index_mem s1 ss in
            eliminate forall i. contains_app_key st (S.index ss i) with i1
          )
          else
            puts_preserves_non_ref st ss ws s1
        )
    in
    forall_intro_3 aux

#pop-options

let sp_is_mp_snoc (#vcfg:_) (tl: verifiable_log vcfg {length tl > 0})
  : Lemma (requires (let i = length tl - 1 in
                     let tl' = prefix tl i in
                     let e = index tl i in
                     sp_is_mp tl'))
          (ensures (sp_is_mp tl))
  = let i = length tl - 1 in
    let tl' = prefix tl i in
    let e = index tl i in
    let open Zeta.GenericVerifier in
    match e with
    | AddM _ _ _ -> sp_is_mp_snoc_addm tl
    | AddB _ _ _ _ -> sp_is_mp_snoc_addb tl
    | EvictM  _ _ -> sp_is_mp_snoc_evictm tl
    | EvictB  _ _ -> sp_is_mp_snoc_evictb tl
    | EvictBM _ _ _ -> sp_is_mp_snoc_evictbm tl
    | RunApp _  _ _ -> sp_is_mp_snoc_appfn tl
    | _ -> ()

let rec lemma_slot_is_merkle_points_to (#vcfg:_) (tl: verifiable_log vcfg)
  : Lemma (ensures (let st = store tl in
                    slot_points_to_is_merkle_points_to st))
          (decreases (length tl))
  = if length tl = 0 then
      sp_is_mp_empty tl
    else
      let i = length tl - 1 in
      let tl' = prefix tl i in
      lemma_slot_is_merkle_points_to tl';
      sp_is_mp_snoc tl

let empty_log_is_map (#vcfg:_) (tl: verifiable_log vcfg)
  : Lemma (ensures (length tl = 0 ==> is_map (store tl)))
  = if length tl = 0 then
      ()

type rel_pair (vcfg:verifier_config)
  = | RP: tls: verifiable_log vcfg ->
          tlk: HT.verifiable_log vcfg.app {thread_rel tls tlk} -> rel_pair vcfg

let lemma_rel_pair_appfn (#vcfg:_) (rp: rel_pair vcfg) (i: seq_index rp.tls)
  : Lemma (ensures (is_appfn rp.tls i = is_appfn rp.tlk i))
          [SMTPat (is_appfn rp.tls i)]
  = let tls = rp.tls in
    let tlk = rp.tlk in
    eliminate forall i. (index tlk i) = to_logk_entry tls i
    with i

let lemma_rel_pair_to_app_fcr (#vcfg:_) (rp: rel_pair vcfg) (i: seq_index rp.tls {is_appfn rp.tls i})
  : Lemma (ensures (to_app_fcr rp.tls i = to_app_fcr rp.tlk i))
          [SMTPat (to_app_fcr rp.tls i)]
  = let tls = rp.tls in
    let tlk = rp.tlk in
    let es = index tls i in
    let ek = index tlk i in

    lemma_state_transition tls i;
    eliminate forall i. (index tlk i) = to_logk_entry tls i with i;
    assert(ek = to_logk_entry tls i);

    let _vss = state_pre tls i in
    let _vsk = state_pre tlk i in
    eliminate forall i. vtls_rel (state_pre tls i) (state_pre tlk i) with i;
    assert(vtls_rel _vss _vsk);

    lemma_app_res_rel _vss _vsk es

open Zeta.SMap

let s2k (#vcfg:_) (rp: rel_pair vcfg) (i: SA.seq_index (app_fcrs rp.tls))
  : GTot (j:SA.seq_index (app_fcrs rp.tlk){S.index (app_fcrs rp.tls) i = S.index (app_fcrs rp.tlk) j})
  = let i1 = app_fcrs_invmap rp.tls i in
    app_fcrs_map rp.tlk i1

let s2k_mono (#vcfg:_) (rp: rel_pair vcfg)
  : Lemma (ensures (monotonic_prop (hoist_ghost (s2k rp))))
  = let fcrss = app_fcrs rp.tls in
    let f = s2k rp in
    let aux (i j: SA.seq_index fcrss)
      : Lemma (ensures (i < j ==> f i < f j))
      = if i < j then (
          let i1 = app_fcrs_invmap rp.tls i in
          let j1 = app_fcrs_invmap rp.tls j in
          app_fcrs_invmap_monotonic rp.tls i j;
          assert(i1 < j1);
          app_fcrs_map_monotonic rp.tlk i1 j1
        )
    in
    forall_intro_2 aux

let k2s (#vcfg:_) (rp: rel_pair vcfg) (j:SA.seq_index (app_fcrs rp.tlk))
  : GTot (i: SA.seq_index (app_fcrs rp.tls) {S.index (app_fcrs rp.tls) i = S.index (app_fcrs rp.tlk) j})
  = let j1 = app_fcrs_invmap rp.tlk j in
    app_fcrs_map rp.tls j1

let k2s_mono (#vcfg:_) (rp: rel_pair vcfg)
  : Lemma (ensures (monotonic_prop (hoist_ghost (k2s rp))))
  = let fcrsk = app_fcrs rp.tlk in
    let f = k2s rp in
    let aux (i j: SA.seq_index fcrsk)
      : Lemma (ensures (i < j ==> f i < f j))
      = if i < j then (
          let i1 = app_fcrs_invmap rp.tlk i in
          let j1 = app_fcrs_invmap rp.tlk j in
          app_fcrs_invmap_monotonic rp.tlk i j;
          assert (i1 < j1);
          app_fcrs_map_monotonic rp.tls i1 j1
        )
    in
    forall_intro_2 aux

let thread_rel_implies_fcrs_identical (#vcfg:_) (tls: verifiable_log vcfg) (tlk:_ {thread_rel tls tlk})
  : Lemma (ensures (app_fcrs tls == app_fcrs tlk))
  = let rp = RP tls tlk in
    s2k_mono rp;
    k2s_mono rp;
    monotonic_bijection_implies_equal
    (app_fcrs rp.tls)
    (app_fcrs rp.tlk)
    (hoist_ghost (s2k rp))
    (hoist_ghost (k2s rp))
