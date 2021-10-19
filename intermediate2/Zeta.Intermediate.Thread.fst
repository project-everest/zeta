module Zeta.Intermediate.Thread

open FStar.Classical
open Zeta.BinTree
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

    let aux (s:_)
      : Lemma (ensures (slot_state_trans_closure s l (s2k0 s) <> None))
      = let sls' = slot_state_trans_closure s l' (s2k0 s) in

        elim_consistent_log_slot tl' s;
        assert(sls' <> None);

        eliminate forall s. s2ks' s = s2kl' s with s;
        assert(s2ks' s = s2kl' s);

        if S.mem s ss then
          assume(inuse_slot st' s)
    in
    forall_intro aux;
    assert(Logs.consistent_log s2k0 l);
    admit()

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
                    valid_logS_entry s2k e))
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
    assert(valid_logS_entry s2kl e);

    let s2ks = Store.to_slot_state_map _st in
    assert(ssm_feq s2kl s2ks);

    assert(valid_logS_entry s2ks e);

    ()

let sp_is_mp (#vcfg:_) (tl: verifiable_log vcfg)
  = let st = store tl in
    slot_points_to_is_merkle_points_to st

let sp_is_mp_empty (#vcfg:_) (tl: verifiable_log vcfg)
  : Lemma (ensures (length tl = 0 ==> sp_is_mp tl))
  = ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 3 --query_stats"

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
            assume(False); (**)
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

              if d = dx then admit() (**)
              else (
                assume(False);
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
                assume(False);
                assert(slot_points_to_is_merkle_points_to_local st s' s' dx);
                ()
              )
              else (
                assume(False); (**)
                assert(get_slot st s2 = get_slot st1 s2);
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
            assume(points_to_info st1 s1 dx = points_to_info st s1 dx);
            ()
          )
        )
    in
    forall_intro_3 aux

#pop-options

let lemma_slot_is_merkle_points_to (#vcfg:_) (tl: verifiable_log vcfg)
  : Lemma (ensures (let st = store tl in
                    slot_points_to_is_merkle_points_to st))
  = admit()

let empty_log_is_map (#vcfg:_) (tl: verifiable_log vcfg)
  : Lemma (ensures (length tl = 0 ==> is_map (store tl)))
  = admit()
