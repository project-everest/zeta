module Veritas.Intermediate.Verify
open FStar.Classical

let lemma_verify_failed (#vcfg:_) (vs:vtls vcfg) (e:_)
  : Lemma (requires (Failed? vs))
          (ensures (Failed? (verify_step vs e)))
  = ()

let rec lemma_verifiable_implies_prefix_verifiable_aux 
      (#vcfg:_) 
      (vsinit: vtls vcfg) 
      (l: logS _{verifiable vsinit l}) 
      (i: seq_index l):
  Lemma (ensures (let li = prefix l i in
                  verifiable vsinit li))
        (decreases (Seq.length l)) = 
  let n = Seq.length l in
  if n = 0 then ()
  else if i = n - 1 then()
  else
    lemma_verifiable_implies_prefix_verifiable_aux vsinit (prefix l (n - 1)) i

let rec lemma_verifiable_implies_init_valid_aux #vcfg (vsinit: vtls vcfg) (l: logS _):
  Lemma (requires (verifiable vsinit l))
        (ensures (Valid? vsinit))
        (decreases (Seq.length l)) = 
  let n = Seq.length l in
  if n = 0 then ()
  else (
    let l' = prefix l (n - 1) in    
    lemma_verifiable_implies_prefix_verifiable_aux vsinit l (n - 1);
    lemma_verifiable_implies_init_valid_aux vsinit l'
  )

let lemma_verifiable_implies_init_valid (#vcfg:_) (vsinit: vtls vcfg) (l: logS _):
  Lemma (requires (verifiable vsinit l))
        (ensures (Valid? vsinit))
  = lemma_verifiable_implies_init_valid_aux vsinit l

let lemma_verifiable_implies_prefix_verifiable 
      (#vcfg:_) 
      (vsinit: vtls vcfg) 
      (l: logS _{verifiable vsinit l}) 
      (i: seq_index l):
  Lemma (ensures (let li = prefix l i in
                  verifiable vsinit li))
  = lemma_verifiable_implies_prefix_verifiable_aux vsinit l i

let lemma_addm_props (#vcfg:_)
                     (vs:vtls vcfg{Valid? vs})
                     (e:logS_entry _{AddM_S? e}):
  Lemma (requires (Valid? (verify_step vs e)))
        (ensures (let AddM_S s (k,v) s' = e in
                  let st' = thread_store vs in
                  inuse_slot st' s' /\
                  (let k' = stored_key st' s' in
                   is_proper_desc k k' /\
                   is_merkle_key k' /\
                   (let mv' = to_merkle_value (stored_value st' s') in
                    let d = desc_dir k k' in
                    (mv_points_to_none mv' d || 
                     is_desc (mv_pointed_key mv' d) k))))) = 
  let AddM_S s (k, v) s' = e in
  let st' = thread_store vs in
  // assert(inuse_slot st s');
  
  let k' = stored_key st' s' in
  assert(is_proper_desc k k');
  assert(is_merkle_key k');
  let mv' = to_merkle_value (stored_value st' s') in
  let d = desc_dir k k' in
  let dh' = desc_hash_dir mv' d in
  match dh' with
  | Empty -> ()
  | Desc k2 _ _  -> 
    if k2 = k then lemma_desc_reflexive k
    else ()

let lemma_addm_propsB #vcfg (vs':vtls vcfg{Valid? vs'}) (e: logS_entry _ {AddM_S? e}):
  Lemma (requires (Valid? (verify_step vs' e)))
        (ensures (let st' = thread_store vs' in
                  let vs = verify_step vs' e in
                  let st = thread_store vs in
                  let AddM_S s (k,v) s' = e in

                  empty_slot st' s /\
                  inuse_slot st s /\
                  identical_except2 st' st s' s /\
                  (let VStoreE k2 _ am2 _ _ = get_inuse_slot st s in
                   k2 = k /\ am2 = Spec.MAdd))) = 
   let vs = verify_step vs' e in
   let st = thread_store vs in
   let st' = thread_store vs' in
   match e with
   | AddM_S s (k, v) s' ->
     assert(empty_slot st' s);

     let k' = stored_key st' s' in
     let mv' = to_merkle_value (stored_value st' s') in
     let d = desc_dir k k' in
     let dh' = desc_hash_dir mv' d in
     match dh' with
     | Empty -> ()
     | Desc _ _ _ -> ()

let lemma_addm_propsC #vcfg (vs':vtls vcfg{Valid? vs'}) (e: logS_entry _ {AddM_S? e}):
  Lemma (requires (Valid? (verify_step vs' e)))
        (ensures (let st' = thread_store vs' in
                  let vs = verify_step vs' e in
                  let st = thread_store vs in
                  let AddM_S s (k,v) s' = e in
                  inuse_slot st' s' /\
                  inuse_slot st s' /\
                  stored_key st' s' = stored_key st s')) =   
   ()

let lemma_evictm_props #vcfg (vs':vtls vcfg{Valid? vs'}) (e: logS_entry _ {EvictM_S? e}):
  Lemma (requires (Valid? (verify_step vs' e)))
        (ensures (let st' = thread_store vs' in
                  let vs = verify_step vs' e in
                  let st = thread_store vs in
                  let EvictM_S s s' = e in
                  inuse_slot st' s /\ inuse_slot st' s' /\
                  empty_slot st s /\ inuse_slot st s' /\
                  stored_key st s' = stored_key st' s' /\
                  identical_except2 st st' s s')) =  ()

let lemma_evictbm_props #vcfg (vs':vtls vcfg{Valid? vs'}) (e: logS_entry _ {EvictBM_S? e}):
  Lemma (requires (Valid? (verify_step vs' e)))
        (ensures (let st' = thread_store vs' in
                  let vs = verify_step vs' e in
                  let st = thread_store vs in
                  let EvictBM_S s s' _ = e in
                  inuse_slot st' s /\ inuse_slot st' s' /\
                  empty_slot st s /\ inuse_slot st s' /\
                  stored_key st s' = stored_key st' s' /\
                  identical_except2 st st' s s')) = ()

let lemma_init_consistent_log #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l}):
  Lemma (requires (Seq.length l = 0))
        (ensures (let st = thread_store vsinit in
                  let s2kinit = to_slot_state_map st in
                  consistent_log s2kinit l /\
                  (let stend = thread_store (verify vsinit l) in
                   let s2kend = S.to_slot_state_map stend in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2kend s2klog))) = 
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let stend = thread_store (verify vsinit l) in
  let s2kend = S.to_slot_state_map stend in
                   
  let aux (s:slot_id vcfg):
      Lemma (ensures (slot_state_trans_closure s l (s2kinit s) <> None))
            [SMTPat (slot_state_trans_closure s l (s2kinit s))] = 
      ()
  in    
  assert(consistent_log s2kinit l);
  assert(stend == stinit);
  let s2klog = L.to_slot_state_map s2kinit l in  

  let aux (s:slot_id vcfg):
    Lemma (ensures (s2kend s == s2klog s))
          [SMTPat (s2kend s == s2klog s)] = 
    // assert(s2kend s == (if inuse_slot stinit s then Assoc (stored_key stinit s) else Free));      
    ()
  in
  // assert(FE.feq s2kend s2klog);
  ()

let lemma_verifiable_implies_consistent_log_feq_get #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l /\ Seq.length l > 0}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   let st' = thread_store (verify vsinit l') in
                   let s2k' = S.to_slot_state_map st' in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let e = Seq.index l (n - 1) in
                   Get_S? e /\
                   consistent_log s2kinit l' /\
                   consistent_log s2kinit l /\
                   (let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2k s2klog)) = 
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let s2klog = L.to_slot_state_map s2kinit l in
  
  let n = Seq.length l in
  let e = Seq.index l (n - 1) in  
  
  let l' = prefix l (n - 1) in
  let s2klog' = Logs.to_slot_state_map s2kinit l' in
  let vs' = verify vsinit l' in
  let st' = thread_store vs' in
  let s2k' = S.to_slot_state_map st' in

  match e with
  | Get_S s1 k1 v1 ->
    let aux2 (s:slot_id vcfg):
      Lemma (ensures (s2k s == s2klog s)) = 
      let ss0 = s2kinit s in
      let ss' = slot_state_trans_closure s l' ss0 in
      assert(ss' <> None);

      let ss = slot_state_trans_closure s l ss0 in
      assert(ss == slot_state_trans e s (Some?.v ss'));
      assert(s2klog s = Some?.v ss);
      assert(s2k' s = s2klog' s);
      
      if s1 = s then (
        assert(inuse_slot st' s);
        assert(stored_key st' s = stored_key st s);
        assert(s2k' s = s2k s);
        assert(s2klog' s = s2klog s);
        ()
      )
      else (
        assert(s2klog' s = s2klog s);
        assert(vs == vget s1 k1 v1 vs');
        assert(identical_except st st' s1);
          assert(get_slot st s = get_slot st' s);
          assert(inuse_slot st s = inuse_slot st' s);
          
          if inuse_slot st s then (
            assert(stored_key st s = stored_key st' s);
            assert(s2k s = s2k' s);
            ()
          )
          else ()        
      )
    in
    forall_intro aux2;
    assert(FE.feq s2k s2klog);
    ()

let lemma_verifiable_implies_consistent_log_feq_put #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l /\ Seq.length l > 0}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   let st' = thread_store (verify vsinit l') in
                   let s2k' = S.to_slot_state_map st' in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let e = Seq.index l (n - 1) in
                   Put_S? e /\
                   consistent_log s2kinit l' /\
                   consistent_log s2kinit l /\
                   (let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2k s2klog)) = 
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let s2klog = L.to_slot_state_map s2kinit l in
  
  let n = Seq.length l in
  let e = Seq.index l (n - 1) in  
  
  let l' = prefix l (n - 1) in
  let s2klog' = Logs.to_slot_state_map s2kinit l' in
  let vs' = verify vsinit l' in
  let st' = thread_store vs' in
  let s2k' = S.to_slot_state_map st' in

  match e with
  | Put_S s1 k1 v1 ->
    let aux2 (s:slot_id vcfg):
      Lemma (ensures (s2k s == s2klog s)) = 
      let ss0 = s2kinit s in
      let ss' = slot_state_trans_closure s l' ss0 in
      assert(ss' <> None);

      let ss = slot_state_trans_closure s l ss0 in
      assert(ss == slot_state_trans e s (Some?.v ss'));
      assert(s2klog s = Some?.v ss);
      assert(s2k' s = s2klog' s);
      
      if s1 = s then (
        assert(inuse_slot st' s);
        assert(stored_key st' s = stored_key st s);
        assert(s2k' s = s2k s);
        assert(s2klog' s = s2klog s);
        ()
      )
      else (
        assert(s2klog' s = s2klog s);
        assert(vs == vput s1 k1 v1 vs');
        assert(identical_except st st' s1);
          assert(get_slot st s = get_slot st' s);
          assert(inuse_slot st s = inuse_slot st' s);
          
          if inuse_slot st s then (
            assert(stored_key st s = stored_key st' s);
            assert(s2k s = s2k' s);
            ()
          )
          else ()        
      )
    in
    forall_intro aux2;
    assert(FE.feq s2k s2klog);
    ()

let lemma_verifiable_implies_consistent_log_feq_addm #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l /\ Seq.length l > 0}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   let st' = thread_store (verify vsinit l') in
                   let s2k' = S.to_slot_state_map st' in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let e = Seq.index l (n - 1) in
                   AddM_S? e /\
                   consistent_log s2kinit l' /\
                   consistent_log s2kinit l /\
                   (let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2k s2klog)) = 
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let s2klog = L.to_slot_state_map s2kinit l in
  
  let n = Seq.length l in
  let e = Seq.index l (n - 1) in  
  
  let l' = prefix l (n - 1) in
  let s2klog' = Logs.to_slot_state_map s2kinit l' in
  let vs' = verify vsinit l' in
  let st' = thread_store vs' in
  let s2k' = S.to_slot_state_map st' in

  lemma_addm_propsB vs' e;

  match e with
  | AddM_S s1 (k1,_) s2 ->
    let aux (s:slot_id vcfg):
      Lemma (ensures (s2k s == s2klog s)) = 
      let ss0 = s2kinit s in
      let ss' = slot_state_trans_closure s l' ss0 in
      assert(ss' <> None);

      let ss = slot_state_trans_closure s l ss0 in
      assert(ss == slot_state_trans e s (Some?.v ss'));
      assert(s2klog s = Some?.v ss);
      assert(s2k' s = s2klog' s);

      if s1 = s then (
        assert(s2klog s = Assoc k1);
        assert(s2k s = Assoc k1);
        ()
      )
      else if s2 = s then (
        assert(inuse_slot st' s);
        assert(ss = ss');
        assert(s2klog s = s2klog' s);
        lemma_addm_propsC vs' e;
        assert(s2k s = s2k' s);
        ()
      )
      else (     
        assert(ss = ss');
        assert(s2klog s = s2klog' s);
        assert(identical_except2 st st' s1 s2);        
        assert(get_slot st s = get_slot st' s);
        assert(s2k s = s2k' s);
        ()
      )
    in
    forall_intro aux;
    assert(FE.feq s2k s2klog);
    ()

let lemma_verifiable_implies_consistent_log_feq_addb #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l /\ Seq.length l > 0}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   let st' = thread_store (verify vsinit l') in
                   let s2k' = S.to_slot_state_map st' in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let e = Seq.index l (n - 1) in
                   AddB_S? e /\
                   consistent_log s2kinit l' /\
                   consistent_log s2kinit l /\
                   (let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2k s2klog)) = 
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let s2klog = L.to_slot_state_map s2kinit l in
  
  let n = Seq.length l in
  let e = Seq.index l (n - 1) in  
  
  let l' = prefix l (n - 1) in
  let s2klog' = Logs.to_slot_state_map s2kinit l' in
  let vs' = verify vsinit l' in
  let st' = thread_store vs' in
  let s2k' = S.to_slot_state_map st' in

  match e with
  | AddB_S s1 (k1,_) _ _ ->
    let aux (s:slot_id vcfg):
      Lemma (ensures (s2k s == s2klog s)) = 
      let ss0 = s2kinit s in
      let ss' = slot_state_trans_closure s l' ss0 in
      assert(ss' <> None);

      let ss = slot_state_trans_closure s l ss0 in
      assert(ss == slot_state_trans e s (Some?.v ss'));
      assert(s2klog s = Some?.v ss);
      assert(s2k' s = s2klog' s);
      if s1 = s then (
        assert(s2klog s = Assoc k1);
        assert(s2k s = Assoc k1);
        ()
      )
      else (
        assert(ss' = ss);
        assert(s2klog s = s2klog' s);
        assert(s2k s = s2k' s);
        ()
      )
    in
    forall_intro aux;
    assert(FE.feq s2k s2klog);
    ()

let lemma_verifiable_implies_consistent_log_feq_evictm #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l /\ Seq.length l > 0}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   let st' = thread_store (verify vsinit l') in
                   let s2k' = S.to_slot_state_map st' in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let e = Seq.index l (n - 1) in
                   EvictM_S? e /\
                   consistent_log s2kinit l' /\
                   consistent_log s2kinit l /\
                   (let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2k s2klog)) = 
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let s2klog = L.to_slot_state_map s2kinit l in
  
  let n = Seq.length l in
  let e = Seq.index l (n - 1) in  
  
  let l' = prefix l (n - 1) in
  let s2klog' = Logs.to_slot_state_map s2kinit l' in
  let vs' = verify vsinit l' in
  let st' = thread_store vs' in
  let s2k' = S.to_slot_state_map st' in
  match e with
  | EvictM_S s1 s2 ->
    let aux (s:slot_id vcfg):
      Lemma (ensures (s2k s == s2klog s)) = 
      let ss0 = s2kinit s in
      let ss' = slot_state_trans_closure s l' ss0 in
      assert(ss' <> None);

      let ss = slot_state_trans_closure s l ss0 in
      assert(ss == slot_state_trans e s (Some?.v ss'));
      assert(s2klog s = Some?.v ss);
      assert(s2k' s = s2klog' s);
      lemma_evictm_props vs' e;
      
      if s1 = s then (
        assert(empty_slot st s);
        assert(s2k s = Free);
        assert(s2klog s = Free);
        ()
      )
      else if s2 = s then (
        assert(s2klog s = s2klog' s);
        assert(s2k s = s2k' s);
        ()
      )
      else (
        assert(ss = ss');      
        assert(s2klog s = s2klog' s);                
        assert(identical_except2 st st' s1 s2);
        assert(get_slot st s = get_slot st' s);
        assert(s2k s = s2k' s);        
        ()
      )
    in
    forall_intro aux;
    assert(FE.feq s2k s2klog);    
    ()

let lemma_verifiable_implies_consistent_log_feq_evictb #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l /\ Seq.length l > 0}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   let st' = thread_store (verify vsinit l') in
                   let s2k' = S.to_slot_state_map st' in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let e = Seq.index l (n - 1) in
                   EvictB_S? e /\
                   consistent_log s2kinit l' /\
                   consistent_log s2kinit l /\
                   (let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2k s2klog)) = 
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let s2klog = L.to_slot_state_map s2kinit l in
  
  let n = Seq.length l in
  let e = Seq.index l (n - 1) in  
  
  let l' = prefix l (n - 1) in
  let s2klog' = Logs.to_slot_state_map s2kinit l' in
  let vs' = verify vsinit l' in
  let st' = thread_store vs' in
  let s2k' = S.to_slot_state_map st' in

  match e with
  | EvictB_S s1 _ ->
    let aux (s:slot_id vcfg):
      Lemma (ensures (s2k s == s2klog s)) = 
      let ss0 = s2kinit s in
      let ss' = slot_state_trans_closure s l' ss0 in
      assert(ss' <> None);

      let ss = slot_state_trans_closure s l ss0 in
      assert(ss == slot_state_trans e s (Some?.v ss'));
      assert(s2klog s = Some?.v ss);
      assert(s2k' s = s2klog' s);

      if s1 = s then (
        assert(empty_slot st s);
        assert(s2k s = Free);
        assert(s2klog s = Free);
        ()
      )
      else (
        assert(ss = ss');
        assert(s2klog s = s2klog' s);
        assert(identical_except st st' s1);
        assert(s2k s = s2k' s);
        ()
      )
    in
    forall_intro aux;
    assert(FE.feq s2k s2klog);
    ()

let lemma_verifiable_implies_consistent_log_feq_evictbm #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l /\ Seq.length l > 0}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   let st' = thread_store (verify vsinit l') in
                   let s2k' = S.to_slot_state_map st' in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let e = Seq.index l (n - 1) in
                   EvictBM_S? e /\
                   consistent_log s2kinit l' /\
                   consistent_log s2kinit l /\
                   (let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2k s2klog)) = 
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let s2klog = L.to_slot_state_map s2kinit l in
  
  let n = Seq.length l in
  let e = Seq.index l (n - 1) in  
  
  let l' = prefix l (n - 1) in
  let s2klog' = Logs.to_slot_state_map s2kinit l' in
  let vs' = verify vsinit l' in
  let st' = thread_store vs' in
  let s2k' = S.to_slot_state_map st' in
  lemma_evictbm_props vs' e;

  match e with
  | EvictBM_S s1 s2 _ ->
    let aux (s:slot_id vcfg):
      Lemma (ensures (s2k s == s2klog s)) = 
      let ss0 = s2kinit s in
      let ss' = slot_state_trans_closure s l' ss0 in
      assert(ss' <> None);

      let ss = slot_state_trans_closure s l ss0 in
      assert(ss == slot_state_trans e s (Some?.v ss'));
      assert(s2klog s = Some?.v ss);
      assert(s2k' s = s2klog' s);
      if s1 = s then (
        assert(empty_slot st s);
        assert(s2k s = Free);
        assert(s2klog s = Free);
        ()
      )
      else if s2 = s then (
        assert(s2klog s = s2klog' s);
        assert(s2k s = s2k' s);
        ()
      )
      else (
        assert(ss = ss');      
        assert(s2klog s = s2klog' s);                
        assert(identical_except2 st st' s1 s2);
        assert(get_slot st s = get_slot st' s);
        assert(s2k s = s2k' s);        
        ()      
      )
    in
    forall_intro aux;
    assert(FE.feq s2k s2klog);
    ()

let lemma_verifiable_implies_consistent_log_feq #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l /\ Seq.length l > 0}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   let st' = thread_store (verify vsinit l') in
                   let s2k' = S.to_slot_state_map st' in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   consistent_log s2kinit l' /\
                   consistent_log s2kinit l /\
                   (let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2k s2klog)) = 
  let n = Seq.length l in
  let e = Seq.index l (n - 1) in  
  match e with
  | Get_S _ _ _ -> lemma_verifiable_implies_consistent_log_feq_get vsinit l
  | Put_S _ _ _ -> lemma_verifiable_implies_consistent_log_feq_put vsinit l
  | AddM_S _ _ _ -> lemma_verifiable_implies_consistent_log_feq_addm vsinit l
  | EvictM_S _ _ -> lemma_verifiable_implies_consistent_log_feq_evictm vsinit l
  | AddB_S _ _ _ _ -> lemma_verifiable_implies_consistent_log_feq_addb vsinit l
  | EvictB_S _ _ -> lemma_verifiable_implies_consistent_log_feq_evictb vsinit l
  | EvictBM_S _ _ _ -> lemma_verifiable_implies_consistent_log_feq_evictbm vsinit l

let lemma_verifiable_implies_consistent_extend #vcfg (vsinit: vtls vcfg) (l: logS _{Seq.length l > 0 /\ verifiable vsinit l}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   consistent_log s2kinit l' /\
                   (let st' = thread_store (verify vsinit l') in
                    let s2k' = S.to_slot_state_map st' in
                    let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                  consistent_log s2kinit l)) = 
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let n = Seq.length l in  
  let l' = prefix l (n - 1) in
  let e = Seq.index l (n - 1) in
  let s2klog' = Logs.to_slot_state_map s2kinit l' in
  let vs' = verify vsinit l' in
  let st' = thread_store vs' in
  let s2k' = S.to_slot_state_map st' in
                  
  let aux (s: slot_id vcfg):
    Lemma (ensures (slot_state_trans_closure s l (s2kinit s) <> None))
          [SMTPat (slot_state_trans_closure s l (s2kinit s))] = 
    let ss0 = s2kinit s in
    let ss' = slot_state_trans_closure s l' ss0 in
    assert(ss' <> None);

    let ss = slot_state_trans_closure s l ss0 in
    assert(ss == slot_state_trans e s (Some?.v ss'));
    match e with
    | Get_S s1 k1 _ ->
      if s1 = s then (
         assert(inuse_slot st' s1);
         assert(stored_key st' s1 = k1);
         assert(s2k' s1 = Assoc k1);
         ()
      )
      else ()
    | Put_S s1 k1 _ ->
      if s1 = s then (
         assert(inuse_slot st' s1);
         assert(stored_key st' s1 = k1);
         assert(s2k' s1 = Assoc k1);
         ()
      )
      else ()      
    | AddM_S s1 (k1,v1) s2 ->
      if s1 = s then (
         assert(empty_slot st' s1);
         assert(s2k' s1 = Free);
         ()
      )
      else if s2 = s then (
        assert(inuse_slot st' s);
        assert(Assoc? (s2k' s));
        ()
      ) 
      else ()    
    | AddB_S s1 (k1,_) _ _ ->
      if s1 = s then (
         assert(empty_slot st' s);
         assert(s2k' s = Free);
         ()
      )
      else ()
    | EvictM_S s1 s2 ->
      assert(inuse_slot st' s1);
      assert(inuse_slot st' s2);
      assert(Assoc? (s2k' s1));
      assert(Assoc? (s2k' s2));
      ()
    | EvictB_S s1 _ ->
      assert(inuse_slot st' s1);
      assert(Assoc? (s2k' s1));
      ()

    | EvictBM_S s1 s2 _ ->
      assert(inuse_slot st' s1);
      assert(inuse_slot st' s2);
      assert(Assoc? (s2k' s1));
      assert(Assoc? (s2k' s2));
      ()    
  in
  assert(consistent_log s2kinit l);      
  ()

let rec lemma_verifiable_implies_consistent_log_aux (#vcfg:_) (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l}):
  Lemma (ensures (let st = thread_store vsinit in
                  let s2kinit = to_slot_state_map st in
                  consistent_log s2kinit l /\
                  (let stend = thread_store (verify vsinit l) in
                   let s2kend = S.to_slot_state_map stend in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2kend s2klog)))
        (decreases (Seq.length l)) = 
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let n = Seq.length l in
  if n = 0 then
     lemma_init_consistent_log vsinit l
  else (
    let l' = prefix l (n - 1) in
    let e = Seq.index l (n - 1) in
    lemma_verifiable_implies_consistent_log_aux vsinit l';
    assert(consistent_log s2kinit l');
    lemma_verifiable_implies_consistent_extend vsinit l;
    assert(consistent_log s2kinit l);    
    lemma_verifiable_implies_consistent_log_feq vsinit l
  )

(* verifiability implies consistency of the log *)
let lemma_verifiable_implies_consistent_log (#vcfg:_) (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l}):
  Lemma (ensures (let st = thread_store vsinit in
                  let s2k = to_slot_state_map st in
                  consistent_log s2k l))
  = lemma_verifiable_implies_consistent_log_aux vsinit l

(* the association of slot -> keys in store is what is mandated by the log *)
let lemma_s2k_store_eq_s2k_log (#vcfg:_) (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l}):
  Lemma (ensures (let stinit = thread_store vsinit in
                  let s2kinit = S.to_slot_state_map stinit in 
                  let stend = thread_store (verify vsinit l) in
                  let s2kend = S.to_slot_state_map stend in
                  let s2klog = L.to_slot_state_map s2kinit l in
                  FE.feq s2kend s2klog))
   = lemma_verifiable_implies_consistent_log_aux vsinit l

let lemma_verifiable_implies_slot_is_merkle_points_to_get (#vcfg:_) 
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _{Get_S? e}):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e)))) =           
  ()

let lemma_verifiable_implies_slot_is_merkle_points_to_put (#vcfg:_) 
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _{Put_S? e}):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e)))) = 
  let st = thread_store vs in
  let vs1 = verify_step vs e in
  let st1 = thread_store vs1 in

  let aux (s1 s2: slot_id _) (d: bin_tree_dir):
    Lemma (slot_points_to_is_merkle_points_to_local st1 s1 s2 d) = 
    assert(slot_points_to_is_merkle_points_to_local st s1 s2 d);
    ()  
  in
  forall_intro_3 aux;
  ()

noeq type sam (#vcfg: verifier_config)  =
  | SAM: vs': vtls vcfg {Valid? vs'} ->
         e: logS_entry _ {AddM_S? e /\ Valid? (verify_step vs' e)} -> sam #vcfg

let am_key #vcfg (a: sam #vcfg) = 
  match a with
  | SAM vs' (AddM_S _ (k,_) _) -> k

let am_slot #vcfg (a: sam #vcfg) =
  match a with
  | SAM vs' (AddM_S s _ _) -> s

let am_anc_slot #vcfg (a: sam #vcfg) = 
  match a with
  | SAM vs' (AddM_S _ _ s') -> s'

let am_store_pre #vcfg (a: sam #vcfg) = 
  match a with
  | SAM vs' _ -> thread_store vs'

let am_store_post #vcfg (a: sam #vcfg) =
  match a with
  | SAM vs' e -> thread_store (verify_step vs' e)

let am_anc_key #vcfg (a: sam #vcfg): Tot (k':key {is_proper_desc (am_key a) k'}) = 
  match a with
  | SAM vs' e ->
    lemma_addm_props vs' e;
    let st' = am_store_pre a in
    stored_key st' (am_anc_slot a)

let am_anc_val_pre #vcfg (a: sam #vcfg) =   
  let st' = am_store_pre a in  
  let s' = am_anc_slot a in
  to_merkle_value (stored_value st' s')

let am_dir #vcfg (a: sam #vcfg): bin_tree_dir = 
  let k = am_key a in
  let k' = am_anc_key a in
  desc_dir k k'

let lemma_addm_anc_pre #vcfg (a: sam #vcfg):
  Lemma (ensures (let mv' = am_anc_val_pre a in
                  let d = am_dir a in
                  let k = am_key a in
                  mv_points_to_none mv' d ||
                  is_desc (mv_pointed_key mv' d) k)) =
  match a with
  | SAM vs' e ->
    lemma_addm_props vs' e;    
    ()

let is_anc_empty #vcfg (a: sam #vcfg) = 
  let mv' = am_anc_val_pre a in
  let d = am_dir a in
  mv_points_to_none mv' d

let am_val_pre #vcfg (a: sam #vcfg): value_type_of (am_key a) = 
  match a with
  | SAM vs' (AddM_S _ (_,v) _) -> v

let am_val_post #vcfg (a: sam #vcfg): value_type_of (am_key a) = 
  let st = am_store_post a in
  let s = am_slot a in
  stored_value st s

let lemma_anc_empty #vcfg (a: sam #vcfg{is_anc_empty a}):
  Lemma (ensures (let v = am_val_pre a in
                  let k = am_key a in
                  let st = am_store_post a in
                  let s = am_slot a in
                  v = init_value k /\
                  v = am_val_post a /\
                  points_to_none st s Left /\
                  points_to_none st s Right)) = ()

let am_anc_val_post #vcfg (a: sam #vcfg): merkle_value =
  let st = am_store_post a in
  let s' = am_anc_slot a in
  to_merkle_value (stored_value st s')

let lemma_anc_empty2 #vcfg (a: sam #vcfg{is_anc_empty a}):
  Lemma (ensures (let st = am_store_post a in
                  let d = am_dir a in
                  let mv = am_anc_val_post a in
                  let k = am_key a in
                  let s' = am_anc_slot a in
                  let s = am_slot a in
                  mv_points_to mv d k /\
                  points_to_dir st s' d s)) = ()

let direct_anc #vcfg (a: sam #vcfg): bool =
  let mv' = am_anc_val_pre a in
  let d = am_dir a in
  let k = am_key a in
  mv_points_to_some mv' d && mv_pointed_key mv' d = k

let lemma_anc_dir #vcfg (a: sam #vcfg{direct_anc a}):
  Lemma (ensures (let s = am_slot a in
                  let st = am_store_post a in
                  am_val_pre a = am_val_post a /\
                  points_to_none st s Left /\
                  points_to_none st s Right)) = ()

let lemma_addm_propsD #vcfg (vs': vtls vcfg) (e: logS_entry _{AddM_S? e}):
  Lemma (requires (Valid? vs' /\ Valid? (verify_step vs' e)))
        (ensures (lemma_addm_props vs' e;
                  let AddM_S s (k,v) s' = e in
                  let st' = thread_store vs' in
                  let k' = stored_key st' s' in
                  let d = desc_dir k k' in
                  let od = other_dir d in
                  let vs = verify_step vs' e in
                  let st = thread_store vs in

                  points_to_none st s od /\
                  points_to_info st s d = points_to_info st' s' d
                  )) = 
  admit()
                  
let lemma_verifiable_implies_slot_is_merkle_points_to_addm (#vcfg:_) 
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _{AddM_S? e}):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e)))) = 
  admit()

(*
  let vs1 = verify_step vs e in
  let st1 = thread_store vs1 in
    // lemma_addm_propsB vs e;
    // lemma_addm_propsC vs e;

  match e with
  | AddM_S s r s' ->
    let st = thread_store vs in


    assert(identical_except2 st st1 s' s);
    assert(vs1 == vaddm s r s' vs);
    
    let k' = stored_key st s' in
    let d = desc_dir k k' in
    let v' = to_merkle_value (stored_value st s') in
    let dh' = desc_hash_dir v' d in
    let h = hashfn v in
    let aux (s1 s2: slot_id _) (d: bin_tree_dir):
      Lemma (slot_points_to_is_merkle_points_to_local st1 s1 s2 d) = 
      assert(slot_points_to_is_merkle_points_to_local st s1 s2 d);

      if not (points_to_dir st1 s1 d s2) then ()
      else if s1 = s then (
        assert(dh' <> Empty);
        match dh' with 
        | Desc k2 h2 b2 ->
          assert(k2 <> k);
          assert(is_proper_desc k2 k);
          let d2 = desc_dir k2 k in
          let mv = to_merkle_value v in
          let mv_upd = Spec.update_merkle_value mv d2 k2 h2 b2 in
          let v'_upd = Spec.update_merkle_value v' d k h false in
                      let st_upd =  if points_to_some_slot st s' d then 
                            madd_to_store_split st s k v s' d d2
                          else
                            madd_to_store st s k (MVal mv_upd) s' d in
            let st_upd = update_value st_upd s' (MVal v'_upd) in
            let vs1c =  update_thread_store vs st_upd in
          //assert(vs1c == vs1);
          admit()
          
      )
      else if s1 = s' then admit()
      else (
        assert(get_slot st s1 = get_slot st1 s1);
        assert(points_to_dir st s1 d s2);
        ()
      )
    
    in
    forall_intro_3 aux;
    ()
*)


let lemma_verifiable_implies_slot_is_merkle_points_to_evictm (#vcfg:_) 
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _{EvictM_S? e}):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e)))) = 
  admit()

let lemma_verifiable_implies_slot_is_merkle_points_to_addb (#vcfg:_) 
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _{AddB_S? e}):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e)))) = 
  admit()

let lemma_verifiable_implies_slot_is_merkle_points_to_evictb (#vcfg:_) 
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _{EvictB_S? e}):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e)))) = 
  admit()

let lemma_verifiable_implies_slot_is_merkle_points_to_evictbm (#vcfg:_) 
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _{EvictBM_S? e}):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e)))) = 
  admit()


(* if there are no verification failures, slot_points to implies merkle points to property is 
 * propagates *)
let lemma_verifiable_implies_slot_is_merkle_points_to (#vcfg:_) 
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e)))) = 
  match e with
  | Get_S s k v -> lemma_verifiable_implies_slot_is_merkle_points_to_get vs e
  | _ -> admit()

let lemma_vget_simulates_spec 
      (#vcfg:_)
      (vss:vtls vcfg{Valid? vss})
      (vsk:Spec.vtls)      
      (e:logS_entry vcfg{Get_S? e})
  : Lemma (requires (vtls_rel vss vsk /\                     
                     valid_logS_entry vss e))
          (ensures (let ek = to_logK_entry vss e in          
                    vtls_rel (verify_step vss e) (Spec.t_verify_step vsk ek))) = ()

let lemma_vget_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{Get_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))
  = ()

let lemma_vput_simulates_spec 
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)      
      (e:logS_entry vcfg{Put_S? e})
  : Lemma (requires (vtls_rel vs vs' /\                     
                     valid_logS_entry vs e))
          (ensures (let ek = to_logK_entry vs e in          
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek))) = ()

let lemma_vput_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{Put_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))
  = ()

(* adding a key not in store to vaddm preserves the spec relationship *)
let lemma_vaddm_preserves_spec_new_key
      (#vcfg:_)
      (vss:vtls vcfg{Valid? vss})
      (vsk:Spec.vtls)
      (e:logS_entry _{AddM_S? e})
  : Lemma (requires (let sts = thread_store vss in
                     let AddM_S _ (k,_) _ = e in
                     vtls_rel vss vsk /\
                     valid_logS_entry vss e /\
                     not (store_contains_key sts k)))
          (ensures (let ek = to_logK_entry vss e in
                    vtls_rel (verify_step vss e) (Spec.t_verify_step vsk ek))) = 
  let sts = thread_store vss in
  let stk = Spec.thread_store vsk in
  let s2k = S.to_slot_state_map sts in
  let ek = to_logK_entry vss e in
  match e with
  | AddM_S s (k,v) s' ->
    (* otherwise e would not be a valid log entry *)
    assert(empty_slot sts s && inuse_slot sts s');

    let k' = stored_key sts s' in
    assert(ek = Spec.AddM (k,v) k');

    (* both intermediate and spec fail if k is not a desc of k' *)
    if not (is_proper_desc k k') then ()

    (* if the value is not compatible both int/spec fail *)
    else if not (is_value_of k v) then ()

    else (
      (* because sts and stk are related, the value associated with k' in slot s' correspond *)
      assert(stored_value sts s' = Spec.stored_value stk k');

      let v' = to_merkle_value (stored_value sts s') in
      let d = desc_dir k k' in
      let dh' = desc_hash_dir v' d in
      match dh' with
      | Empty -> 
        (* both fail *)
        if v <> init_value k then ()
        
        else 
          admit()
      | _ ->
      admit()
    )

(* if the key is not present in store and store is a map, then store remains a map after add *)
let lemma_vaddm_preserves_ismap_new_key
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{AddM_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let AddM_S _ (k,_) _ = e in
                     not (store_contains_key st k)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))
   = admit()

(* addb preserves spec relationship if the kew is not in store *)
let lemma_vaddb_preserves_spec_new_key
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)      
      (e:logS_entry _{AddB_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let AddB_S _ (k,_) _ _ = e in
                     vtls_rel vs vs' /\
                     valid_logS_entry vs e /\
                     not (store_contains_key st k)))
          (ensures (let ek = to_logK_entry vs e in
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek))) = admit()

(* if the key is not present in store and store is a map, then store remains a map after add *)
let lemma_vaddb_preserves_ismap_new_key
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{AddB_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let AddB_S _ (k,_) _ _ = e in
                     not (store_contains_key st k)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))
  = admit()

let lemma_evictb_simulates_spec 
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)      
      (e:logS_entry vcfg{EvictB_S? e})
  : Lemma (requires (vtls_rel vs vs' /\                     
                     valid_logS_entry vs e))
          (ensures (let ek = to_logK_entry vs e in          
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))
  = admit()

let lemma_evictb_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{EvictB_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))
  = admit()

let lemma_evictm_simulates_spec
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)      
      (e:logS_entry vcfg{EvictM_S? e})
  : Lemma (requires (let st = thread_store vs in
                     vtls_rel vs vs' /\                     
                     valid_logS_entry vs e /\
                     slot_points_to_is_merkle_points_to st))
          (ensures (let ek = to_logK_entry vs e in          
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))  
   = admit()

let lemma_evictm_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{EvictM_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))
  = admit()

let lemma_evictbm_simulates_spec
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)      
      (e:logS_entry vcfg{EvictBM_S? e})
  : Lemma (requires (let st = thread_store vs in
                     vtls_rel vs vs' /\                     
                     valid_logS_entry vs e /\
                     slot_points_to_is_merkle_points_to st))
          (ensures (let st = thread_store vs in
                    let s2k = S.to_slot_state_map st in
                    let ek = to_logK_entry vs e in          
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))  
  = admit()

let lemma_evictbm_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{EvictBM_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))
  = admit()

(*



(* Simulation lemmas for v* functions *)

let lemma_vaddm_simulates_spec_if_k_is_new
  #vcfg
  (vss:vtls vcfg{Valid? vss})
  (vsk:Spec.vtls{Spec.Valid? vsk})
  (s: empty_slot_id (thread_store vss))
  (s':inuse_slot_id (thread_store vss))
  (r: record)
  : Lemma (requires (let sts = thread_store vss in
                     let (k,v) = r in
                     let k' = stored_key sts s' in
                     not (store_contains_key sts k) /\
                     vtls_rel vss vsk /\
                     is_merkle_key k' /\
                     is_map sts))
          (ensures (let sts = thread_store vss in
                    let (k,v) = r in
                    let k' = stored_key sts s' in
                    let vss' = vaddm s r s' vss in
                    (vtls_rel vss' (Spec.vaddm r k' vsk)) /\
                     (Valid? vss' ==> is_map (thread_store vss')))) = 
  let sts = thread_store vss in                    
  let stk = Spec.thread_store vsk in
  assert(store_rel sts stk);

  let (k,v) = r in
  let k' = stored_key sts s' in

  (* if k' is not an ancestor both intermediate & spec fail *)
  if not (is_proper_desc k k') then ()

  (* if v is not compatible with k then both fail *)
  else if not (is_value_of k v) then ()

  else (
    lemma_as_map_slot_key_equiv sts s' k';
    assert(stored_value sts s' = Spec.stored_value stk k');

    let v' = to_merkle_value (stored_value sts s') in    
    let d = desc_dir k k' in
         
    admit()
  )

let t_verify #vcfg (id:thread_id) (l:logS vcfg): vtls vcfg = 
  fst (t_verify_aux (init_thread_state id) l) 

(*
let rec lemma_slot_points_to_implies_mv_points_to
  #vcfg
  (tl:tl_verifiable_log #vcfg)
  (s1:slot_id vcfg)
  (s2:slot_id vcfg)
  (d: bin_tree_dir)
  : Lemma (requires (let vs = verify tl in
                     let st = thread_store vs in                     
                     points_to_dir s1 d s2))
          (ensures (let vs = verify tl in
                    let st = thread_store vs in
                    let k1 = stored_key st s1 in
                    let k2 = stored_key st s2 in
                    is_merkle_key k1 /\
                    (let v1 = to_merkle_value (stored_value st s1) in
                     mv_points_to v1 d k2))) = admit()
*)

(* 
 * if we start with a store that is a map and a key in store that 
 * has been added with Merkle, then adding the key again using addm fails
 *)
let lemma_vaddm_dupliate_key_fails
  #vcfg
  (vs:vtls vcfg{Valid? vs})
  (s:empty_slot_id (thread_store vs))
  (s':slot_id vcfg)
  (r:record)
  : Lemma (requires (let st = thread_store vs in
                     let (k,v) = r in
                     is_map st /\
                     store_contains_key st k /\
                     (let sk = slot_of_key st k in
                      let am = add_method_of st sk in
                      am = Spec.MAdd)))
           (ensures (Failed? (vaddm s r s' vs))) = 
  let st = thread_store vs in
  let (k,v) = r in
  let sk = slot_of_key st k in
  let am = add_method_of st sk in

  (* if slot s' is empty then addm fails since ancestor slot is empty *)
  if empty_slot st s' then ()
  else
    let k' = stored_key st s' in
    (* k' is a proper ancestor, otherwise we fail so nothing to prove *)
    if not (is_proper_desc k k') then ()
    else (
      (* k cannot be root *)
      assert(k <> Root);
      
      let sk' = pointed_slot st sk in
  
      admit()
    )


(*
*)                   

(*
// TODO: flaky
#push-options "--z3rlimit_factor 2"
let lemma_vaddm_simulates_spec_if_k_is_new
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (r:record)
      (k':merkle_key)  
   : Lemma (requires (s < thread_store_size vs /\
                      not (store_contains (thread_store vs) s) /\
                      not (store_contains_key (thread_store vs) (fst r)) /\ // key is new
                      vtls_rel vs vs' /\ 
                      slot_key_rel vs s' k' /\
                      store_inv (thread_store vs)))
           (ensures (vtls_rel (vaddm s r s' vs) (Spec.vaddm r k' vs'))) 
  = ()
#pop-options

(* st satisfies store_inv everywhere except for slot s, direction d 
   --> this is helpful in the vaddm and vevictm proofs because it allows us to
       say that the invariant is partially-satisfied in the middle of a step
*)
let store_inv_except (st:vstore) (s:instore_merkle_slot st) (d:bin_tree_dir)
  = is_map st /\
    (forall (s0:instore_merkle_slot st) 
       (d0:bin_tree_dir{points_to_some st s0 d0 /\ ~ (s = s0 /\ d = d0)}).
         let k0 = pointed_key st s0 d0 in
         in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0)

(* updating a merkle value to point to a new key preserves the invariant *)
let lemma_update_merkle_value_to_point_to_new_key_preserves_inv
      (st:vstore)
      (s:instore_merkle_slot st)
      (k:key{not (store_contains_key_with_MAdd st k)})
      (d:bin_tree_dir)
      (h:ms_hash_value)
      (b:bool)
  : Lemma (requires (store_inv st))
          (ensures (let v = to_merkle_value (stored_value st s) in
                    let v_upd = Spec.update_merkle_value v d k h b in
                    let st_upd = update_value st s (MVal v_upd) in  
                    store_inv_except st_upd s d))
  = let v = to_merkle_value (stored_value st s) in
    let v_upd = Spec.update_merkle_value v d k h b in
    let st_upd = update_value st s (MVal v_upd) in
    let aux (s0:instore_merkle_slot st_upd) 
            (d0:bin_tree_dir{points_to_some st_upd s0 d0 /\ ~ (s0 = s /\ d0 = d)}) 
      : Lemma (let k0 = pointed_key st_upd s0 d0 in
               in_store_bit st_upd s0 d0 = store_contains_key_with_MAdd st_upd k0)
      = let k0 = pointed_key st s0 d0 in
        assert (in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0) in
    Classical.forall_intro_2 aux

(* some useful properties that follow from EAC
   
   NOTE: we could also prove other_dir_does_not_point_to using properties
   of the intermediate-level functions, but I don't think we can maintain the
   no_other_slot_points_to constraint *)
let no_other_slot_points_to (st:vstore) (s:instore_merkle_slot st) (k:key)
  = forall (s':instore_merkle_slot st{s <> s'}) (d:bin_tree_dir{points_to_some st s' d}). 
      pointed_key st s' d <> k

let other_dir_does_not_point_to (st:vstore) (s:instore_merkle_slot st) (d:bin_tree_dir) (k:key)
  = not (points_to_some st s (other_dir d)) || 
    pointed_key st s (other_dir d) <> k

(* when adding a new (k,v) pair, we need to satisfy a few properties
   to preserve in_store_inv. In particular: 
   * v cannot point to anything in the store via a merkle add
   * v cannot point to k *)
let valid_new_value (st:vstore) (k:key) (v:value_type_of k)
  = MVal? v ==>
    (let mv = to_merkle_value v in
     forall (d:bin_tree_dir{mv_points_to_some mv d}).
       let pk = mv_pointed_key mv d in
       not (store_contains_key_with_MAdd st pk) && pk <> k) 

(* adding a slot requires updating the in_store bit *)
let lemma_add_to_store_update_in_store_preserves_inv1
      (st:vstore)
      (s':instore_merkle_slot st)
      (s:st_index st{not (store_contains st s)})
      (d:bin_tree_dir{points_to_some st s' d})
      (k:key{not (store_contains_key st k)})
      (v:value_type_of k)
  : Lemma (requires (store_inv_except st s' d /\
                     pointed_key st s' d = k /\
                     no_other_slot_points_to st s' k /\
                     other_dir_does_not_point_to st s' d k /\
                     valid_new_value st k v))
          (ensures (let st_upd = add_to_store st s k v Spec.MAdd in
                    let st_upd2 = update_in_store st_upd s' d true in
                    store_inv st_upd2))
  = let st_upd = add_to_store st s k v Spec.MAdd in
    let st_upd2 = update_in_store st_upd s' d true in
    let aux (s0:instore_merkle_slot st_upd2) (d0:bin_tree_dir{points_to_some st_upd2 s0 d0})
      : Lemma (let k0 = pointed_key st_upd2 s0 d0 in
               in_store_bit st_upd2 s0 d0 = store_contains_key_with_MAdd st_upd2 k0)
      = if s0 = s' && d0 = d
        then () // follows from the call to update_in_store
        else if s0 = s
        then () // follows from the constraints on v
        else 
          let k0 = pointed_key st s0 d0 in
          assert (in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0) // follows from store_inv st
      in
    Classical.forall_intro_2 aux

(* modified form of the lemma above used in the third case of vaddm; 
   the lemma above assumes that the added value (v) does not point to anything
   currently in the store, while this lemma assumes that v points to key vk
   in direction vd, which may or may not be in the store (dictated by vd). *)
let lemma_add_to_store_update_in_store_preserves_inv2
      (st:vstore)
      (s':instore_merkle_slot st)
      (s:st_index st{not (store_contains st s)})
      (d:bin_tree_dir{points_to_some st s' d})
      (k:merkle_key{not (store_contains_key st k)})
      (v:merkle_value)
      (vk:key{k <> vk})
      (vd:bin_tree_dir{mv_points_to_some v vd})
      (vb:bool{vb = store_contains_key_with_MAdd st vk})
  : Lemma (requires (store_inv_except st s' d /\
                     pointed_key st s' d = k /\
                     no_other_slot_points_to st s' k /\
                     other_dir_does_not_point_to st s' d k /\
                     Empty? (desc_hash_dir v (other_dir vd)) /\
                     mv_pointed_key v vd = vk))
          (ensures (let st_upd = add_to_store st s k (MVal v) Spec.MAdd in
                    let st_upd2 = update_in_store st_upd s' d true in
                    let st_upd3 = update_in_store st_upd2 s vd vb in
                    store_inv st_upd3))
  = let st_upd = add_to_store st s k (MVal v) Spec.MAdd in
    let st_upd2 = update_in_store st_upd s' d true in
    let st_upd3 = update_in_store st_upd2 s vd vb in
    let aux (s0:instore_merkle_slot st_upd3) (d0:bin_tree_dir{points_to_some st_upd3 s0 d0})
      : Lemma (let k0 = pointed_key st_upd3 s0 d0 in
               in_store_bit st_upd3 s0 d0 = store_contains_key_with_MAdd st_upd3 k0)
      = if s0 = s
        then ()
        else if s0 = s' && d0 = d
        then ()
        else let k0 = pointed_key st s0 d0 in
          assert (in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0) in
    Classical.forall_intro_2 aux

let lemma_update_value_no_other_slot_points_to
      (st:vstore)
      (s:instore_merkle_slot st)
      (k:key)
      (v:value_type_of (stored_key st s))
  : Lemma (requires (no_other_slot_points_to st s k))
          (ensures (no_other_slot_points_to (update_value st s v) s k))
          [SMTPat (no_other_slot_points_to (update_value st s v) s k)]
  = let st_upd = update_value st s v in
    let aux (s0:instore_merkle_slot st_upd{s0 <> s}) (d0:bin_tree_dir{points_to_some st_upd s0 d0})
      : Lemma (pointed_key st_upd s0 d0 <> k)
      = assert (pointed_key st s0 d0 <> k) in
    Classical.forall_intro_2 aux

let lemma_update_in_store_no_other_slot_points_to
      (st:vstore)
      (s:instore_merkle_slot st)
      (k:key)
      (d:bin_tree_dir)
      (b:bool)
  : Lemma (requires (no_other_slot_points_to st s k))
          (ensures (no_other_slot_points_to (update_in_store st s d b) s k))
          [SMTPat (no_other_slot_points_to (update_in_store st s d b) s k)]
  = let st_upd = update_in_store st s d b in
    let aux (s0:instore_merkle_slot st_upd{s0 <> s}) (d0:bin_tree_dir{points_to_some st_upd s0 d0})
      : Lemma (pointed_key st_upd s0 d0 <> k)
      = assert (pointed_key st s0 d0 <> k) in
    Classical.forall_intro_2 aux

let lemma_vaddm_preserves_inv_if_k_is_new
      (vs:vtls{Valid? vs}) 
      (s s':slot_id)
      (r:record)
   : Lemma (requires (Valid? (vaddm s r s' vs) /\
                      (let st = thread_store vs in
                       let k' = stored_key st s' in
                       let (k,v) = r in
                       let d = desc_dir k k' in
                       store_inv st /\
                       // properties below come from EAC
                       ~ (store_contains_key st k) /\ // key is new
                       no_other_slot_points_to st s' k /\ // no slot besides s' points to k
                       other_dir_does_not_point_to st s' d k /\ // s' only points to k in one dir
                       valid_new_value st k v)))
           (ensures (store_inv (thread_store (vaddm s r s' vs)))) 
  = let st = thread_store vs in
    let (k,v) = r in
    let k' = stored_key st s' in
    let v' = to_merkle_value (stored_value st s') in
    let d = desc_dir k k' in
    let dh' = desc_hash_dir v' d in 
    let h = hashfn v in
    match dh' with
    | Empty ->
        let v'_upd = Spec.update_merkle_value v' d k h false in
        let st_upd = update_value st s' (MVal v'_upd) in
        lemma_update_merkle_value_to_point_to_new_key_preserves_inv st s' k d h false;
        lemma_add_to_store_update_in_store_preserves_inv1 st_upd s' s d k v
    | Desc k2 h2 b2 ->
        if k2 = k 
        then lemma_add_to_store_update_in_store_preserves_inv1 st s' s d k v
        else ( 
          let d2 = desc_dir k2 k in
          let inb = in_store_bit st s' d in
          let v_upd = Spec.update_merkle_value (to_merkle_value v) d2 k2 h2 b2 in
          let v'_upd = Spec.update_merkle_value v' d k h false in
          let st_upd = update_value st s' (MVal v'_upd) in
          lemma_update_merkle_value_to_point_to_new_key_preserves_inv st s' k d h false;
          lemma_add_to_store_update_in_store_preserves_inv2 st_upd s' s d k v_upd k2 d2 inb
        )

let lemma_has_instore_merkle_desc (st:vstore) (st':Spec.vstore) (s:slot_id) (k:key)
  : Lemma (requires (store_inv st /\ store_rel st st' /\ slot_key_equiv st s k))
          (ensures (has_instore_merkle_desc st s = Spec.has_instore_merkle_desc st' k))
          [SMTPat (has_instore_merkle_desc st s); SMTPat (Spec.has_instore_merkle_desc st' k)]
  = ()

let lemma_vevictm_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (k:key)
      (k':merkle_key)  
  : Lemma (requires (vtls_rel vs vs' /\ 
                     slot_key_rel vs s k /\ 
                     slot_key_rel vs s' k' /\
                     store_inv (thread_store vs)))
          (ensures (vtls_rel (vevictm s s' vs) (Spec.vevictm k k' vs'))) 
  = ()

(* updating a merkle value preserves the invariant if you leave the pointed-to key the same *)
let lemma_update_merkle_value_with_same_key_preserves_inv
      (st:vstore)
      (s:instore_merkle_slot st)
      (k:key)
      (d:bin_tree_dir{points_to_some st s d})
      (h:ms_hash_value)
      (b:bool)
  : Lemma (requires (store_inv st /\
                     pointed_key st s d = k))
          (ensures (let v = to_merkle_value (stored_value st s) in
                    let v_upd = Spec.update_merkle_value v d k h b in
                    store_inv (update_value st s (MVal v_upd))))
  = let v = to_merkle_value (stored_value st s) in
    let v_upd = Spec.update_merkle_value v d k h b in
    let st_upd = update_value st s (MVal v_upd) in
    let aux (s0:instore_merkle_slot st_upd) (d0:bin_tree_dir{points_to_some st_upd s0 d0})
      : Lemma (let k0 = pointed_key st_upd s0 d0 in
               in_store_bit st_upd s0 d0 = store_contains_key_with_MAdd st_upd k0)
      = let k0 = pointed_key st s0 d0 in
        assert(in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0) in
    Classical.forall_intro_2 aux

(* evicting a slot requires updating the in_store bit *)
let lemma_evict_from_store_update_in_store_preserves_inv
      (st:vstore)
      (s':instore_merkle_slot st)
      (s:slot_id{store_contains st s /\ s <> s'})
      (d:bin_tree_dir{points_to_some st s' d})
  : Lemma (requires (let k = stored_key st s in
                     store_inv st /\
                     pointed_key st s' d = k /\
                     no_other_slot_points_to st s' k /\
                     other_dir_does_not_point_to st s' d k))
          (ensures (let st_upd = evict_from_store st s in
                    store_inv (update_in_store st_upd s' d false)))
  = let st_upd = evict_from_store st s in
    let st_upd2 = update_in_store st_upd s' d false in
    let aux (s0:instore_merkle_slot st_upd2) (d0:bin_tree_dir{points_to_some st_upd s0 d0})
      : Lemma (let k0 = pointed_key st_upd2 s0 d0 in
               in_store_bit st_upd2 s0 d0 = store_contains_key_with_MAdd st_upd2 k0)
      = assert (s0 <> s); // not possible that s0 = s because s is not in the store
        let k0 = pointed_key st_upd2 s0 d0 in
        if s0 = s' && d0 = d
        then (
          assert (not (in_store_bit st_upd2 s0 d0));
          assert (not (store_contains_key_with_MAdd st_upd2 k0))
        ) 
        else if s0 = s' 
        then (
          assert (k0 <> stored_key st s); // by points_to_unique
          assert (in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0)
        ) 
        else (
          assert (pointed_key st s0 d0 <> (stored_key st s)); // by points_to_unique
          assert (k0 <> stored_key st s);
          assert (in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0)
        ) in
    Classical.forall_intro_2 aux

let lemma_vevictm_preserves_inv 
      (vs:vtls{Valid? vs}) 
      (s s':slot_id)
  : Lemma (requires (Valid? (vevictm s s' vs) /\
                     (let st = thread_store vs in 
                      let k = stored_key st s in
                      let k' = stored_key st s' in
                      let d = desc_dir k k' in
                      store_inv st /\
                      pointed_key st s' d = k /\
                      no_other_slot_points_to st s' k /\
                      other_dir_does_not_point_to st s' d k)))
                     (ensures (store_inv (thread_store (vevictm s s' vs)))) 
  = let st = thread_store vs in
    let k = stored_key st s in
    let v = stored_value st s in
    let k' = stored_key st s' in
    let v' = stored_value st s' in
    let d = desc_dir k k' in
    let v' = to_merkle_value v' in
    let dh' = desc_hash_dir v' d in
    let h = hashfn v in
    match dh' with
    | Desc k2 h2 b2 ->
        let v'_upd = Spec.update_merkle_value v' d k h false in
        let st_upd = update_value st s' (MVal v'_upd) in
        lemma_update_merkle_value_with_same_key_preserves_inv st s' k d h false;
        lemma_evict_from_store_update_in_store_preserves_inv st_upd s' s d

let lemma_vaddb_simulates_spec_if_k_is_new 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id)
      (r:record)
      (t:timestamp)
      (j:thread_id)
  : Lemma (requires (s < thread_store_size vs /\ 
                     not (store_contains (thread_store vs) s) /\ 
                     not (store_contains_key (thread_store vs) (fst r)) /\ // key is new
                     vtls_rel vs vs'))
          (ensures (vtls_rel (vaddb s r t j vs) (Spec.vaddb r t j vs')))
  = ()

let lemma_add_to_store_BAdd_preserves_inv
      (st:vstore)
      (s:st_index st{not (store_contains st s)})
      (k:key{not (store_contains_key st k)})
      (v:value_type_of k)
  : Lemma (requires (store_inv st /\
                     valid_new_value st k v))
          (ensures (let st_upd = add_to_store st s k v Spec.BAdd in
                    store_inv st_upd))
  = let st_upd = add_to_store st s k v Spec.BAdd in
    let aux (s0:instore_merkle_slot st_upd) (d0:bin_tree_dir{points_to_some st_upd s0 d0})
      : Lemma (let k0 = pointed_key st_upd s0 d0 in
               in_store_bit st_upd s0 d0 = store_contains_key_with_MAdd st_upd k0)
      = if s0 = s
        then () // follows from the constraints on v
        else 
          let k0 = pointed_key st s0 d0 in
          assert (in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0) // follows from store_inv st
      in
    Classical.forall_intro_2 aux

let lemma_vaddb_preserves_inv_if_k_is_new 
      (vs:vtls{Valid? vs}) 
      (s:slot_id)
      (r:record)
      (t:timestamp)
      (j:thread_id)
  : Lemma (requires (Valid? (vaddb s r t j vs) /\
                     (let st = thread_store vs in
                      let (k,v) = r in
                      store_inv st /\
                      not (store_contains_key st k) /\
                      valid_new_value st k v)))
          (ensures (store_inv (thread_store (vaddb s r t j vs))))
  = lemma_add_to_store_BAdd_preserves_inv (thread_store vs) s (fst r) (snd r)

let lemma_vevictb_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id)
      (k:key)
      (t:timestamp)
  : Lemma (requires (store_inv (thread_store vs) /\ 
                     vtls_rel vs vs' /\ 
                     slot_key_rel vs s k))
          (ensures (vtls_rel (vevictb s t vs) (Spec.vevictb k t vs'))) 
  = ()

(* evicting a blum slot preserves in_store_inv *)
let lemma_evict_from_store_BAdd_preserves_inv
      (st:vstore)
      (s:slot_id{store_contains st s})
  : Lemma (requires (store_inv st /\ add_method_of st s = Spec.BAdd))
          (ensures (store_inv (evict_from_store st s)))
  = let st_upd = evict_from_store st s in
    let aux (s0:instore_merkle_slot st_upd) (d0:bin_tree_dir{points_to_some st_upd s0 d0})
      : Lemma (let k = pointed_key st_upd s0 d0 in
               in_store_bit st_upd s0 d0 = store_contains_key_with_MAdd st_upd k)
      = assert (s0 <> s); 
        let k0 = pointed_key st s0 d0 in
        assert (in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0) in
    Classical.forall_intro_2 aux

let lemma_vevictb_preserves_inv 
      (vs:vtls{Valid? vs}) 
      (s:slot_id)
      (t:timestamp)
  : Lemma (requires (store_inv (thread_store vs) /\
                     Valid? (vevictb s t vs)))
          (ensures (store_inv (thread_store (vevictb s t vs))))
  = lemma_evict_from_store_BAdd_preserves_inv (thread_store vs) s

let lemma_vevictbm_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (k:key)
      (k':merkle_key)
      (t:timestamp)
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k /\ slot_key_rel vs s' k'))
          (ensures (vtls_rel (vevictbm s s' t vs) (Spec.vevictbm k k' t vs'))) 
  = admit() // TODO: suspicious -- why does the unit proof work?

let lemma_vevictbm_preserves_inv 
      (vs:vtls{Valid? vs}) 
      (s s':slot_id)
      (t:timestamp)
  : Lemma (requires (store_inv (thread_store vs) /\ Valid? (vevictbm s s' t vs)))
          (ensures (store_inv (thread_store (vevictbm s s' t vs))))
  = admit() // TODO: VERY suspicious
*)


let lemma_t_verify_step_valid_implies_log_exists (#vcfg:_) (vs:vtls vcfg) (e:logS_entry vcfg)
  : Lemma (requires (Valid? (t_verify_step vs e)))
          (ensures (Some? (logS_to_logK_entry vs e)))
          [SMTPat (Some? (logS_to_logK_entry vs e))]
  = ()


let rec lemma_t_verify_aux_valid_implies_log_exists (#vcfg:_) (vs:vtls vcfg) (l:logS vcfg)
  : Lemma (requires (Valid? (fst (t_verify_aux vs l))))
          (ensures (Some? (snd (t_verify_aux vs l))))
          (decreases (Seq.length l))
  = let n = Seq.length l in
    if n <> 0 
    then lemma_t_verify_aux_valid_implies_log_exists vs (prefix l (n - 1))

(*

let lemma_empty_store_rel () 
  : Lemma (store_rel (empty_store store_size) Spec.empty_store)
  = lemma_as_map_empty store_size

let lemma_init_thread_state_rel (id:thread_id)
  : Lemma (vtls_rel (init_thread_state id) (Spec.init_thread_state id))
  = let vs = Valid id (empty_store store_size) (MkTimestamp 0 0) empty_hash_value empty_hash_value in 
    let vs' = Spec.Valid id Spec.empty_store (MkTimestamp 0 0) Root empty_hash_value empty_hash_value in
    lemma_empty_store_rel ();
    if id = 0 
    then 
      let st = thread_store vs in
      let st' = Spec.thread_store vs' in
      lemma_store_rel_add_to_store st st' 0 Root (init_value Root) Spec.MAdd
*)

let rec lemma_t_verify_aux_valid_implies_prefix_valid
  #vcfg (vs:vtls vcfg) (l:logS vcfg) (i:nat{i <= Seq.length l}):
  Lemma (requires (Valid? (fst (t_verify_aux vs l))))
        (ensures (Valid? (fst (t_verify_aux vs (prefix l i)))))
        (decreases (Seq.length l))
  = let n = Seq.length l in
    if n > 0 && i < n - 1
    then 
      let lp = prefix l (n - 1) in
      lemma_t_verify_aux_valid_implies_prefix_valid  vs lp i

let lemma_tl_verifiable_implies_prefix_verifiable
  (tl:tl_verifiable_log) (i:nat{i <= tl_length tl}):
  Lemma (ensures (tl_verifiable (tl_prefix tl i)))
  = lemma_t_verify_aux_valid_implies_prefix_valid (init_thread_state (fst tl)) (snd tl) i

let lemma_gl_verifiable_implies_prefix_verifiable
  #vcfg (gl:gl_verifiable_log vcfg) (i:nat{i <= Seq.length gl}):
  Lemma (ensures (gl_verifiable (prefix gl i)))
  = let glp = prefix gl i in
    let aux (tid:seq_index glp)
      : Lemma (ensures (Valid? (verify (thread_log glp tid))))
      = assert(thread_log glp tid = thread_log gl tid) in
    Classical.forall_intro aux

(*
let lemma_verifiable_append1  (gl:SpecG.verifiable_log) (l:logK{SpecT.verifiable (Seq.length gl, l)})
  : Lemma (SpecG.verifiable (append1 gl l))
  = let gl' = append1 gl l in
    assert (Seq.length gl' = Seq.length gl + 1);
    let aux (i:seq_index gl') : Lemma (SpecT.verifiable (SpecG.thread_log gl' i))
      = if i < Seq.length gl 
        then assert (SpecT.verifiable (SpecG.thread_log gl i)) in
    Classical.forall_intro aux

*)

let clock_sorted #vcfg (il: il_logS vcfg{il_verifiable il})
  = forall (i j:I.seq_index il). i <= j ==> il_clock il i `ts_leq` il_clock il j

let lemma_prefix_verifiable #vcfg (itsl: its_log vcfg) (i:nat{i <= I.length itsl}):
  Lemma (ensures (il_verifiable (I.prefix itsl i) /\ clock_sorted (I.prefix itsl i)))
  = admit()
// should follow the proof in Veritas.Verifier.TSLog




let t_verify_aux_snoc #vcfg (vs:vtls vcfg) (l:logS vcfg) (e:logS_entry vcfg)
  : Lemma (ensures
             fst (t_verify_aux vs (Seq.snoc l e)) ==
             t_verify_step (fst (t_verify_aux vs l)) e)
  = assert (prefix (Seq.snoc l e) (Seq.length l) `Seq.equal` l)

let lemma_verifier_thread_state_extend #vcfg (il: its_log vcfg) (i: I.seq_index il):
  Lemma (thread_state_post il i == 
         t_verify_step (thread_state_pre il i) (I.index il i))
  = let tid = il_thread_id_of il i in
    let il_i = I.prefix il i in
    let il_i1 = I.prefix il (i + 1) in
    let logS_tid = Seq.index (I.s_seq il_i) tid in
    let logS_tid1 = Seq.index (I.s_seq il_i1) tid in
    I.lemma_prefix_snoc il i;
    assert (logS_tid1 `Seq.equal` Seq.snoc logS_tid (I.index il i));
    let init = init_thread_state tid in
    let lhs = t_verify_aux init logS_tid1 in
    let rhs = t_verify_step (fst (t_verify_aux init logS_tid)) (I.index il i) in
    t_verify_aux_snoc init logS_tid (I.index il i)

#push-options "--fuel 1,1 --ifuel 1,1 --z3rlimit_factor 4"
module SA = Veritas.SeqAux
module I = Veritas.Interleave


let rec ilogS_to_logK #vcfg (il:its_log vcfg) 
  : Tot (sil:SpecTS.il_vlog { same_shape il sil })
        (decreases (I.IL?.prf il))
  = let open I in
    let IL s ss prf = il in
    match prf with
    | IntEmpty ->
      IL _ _ IntEmpty

    | IntAdd s' ss' prf ->
      let il' = IL s' ss' prf in
      assert (Seq.equal ss (append1 ss' Seq.empty));
      assert (forall (tid:Veritas.SeqAux.seq_index ss'). thread_log ss' tid == thread_log ss tid);
      I.i2s_map_int_add il';
      assert (forall (i:I.seq_index il'). il_clock il' i == il_clock il i);
      assert (clock_sorted il');
      let IL _ _ prf = ilogS_to_logK il' in
      let res = IL _ _ (IntAdd _ _ prf) in
      res

    | IntExtend s0 ss0 prf x i ->
      let il' = IL _ _ prf in
      I.hprefix_extend _ _ prf x i;
      lemma_prefix_verifiable il' (I.length il - 1);
      let IL _ ss0' prefix = ilogS_to_logK il' in
      if Seq.length s0 = 0
      then (
        assert (Seq.equal s0 Seq.empty);
        I.interleave_empty prf;
        let vs = init_thread_state i in
        assert (tl_verifiable (thread_log ss0 i));
        assert (Seq.equal (snd (thread_log ss i))
                          (SA.append1 Seq.empty x));    
        assert (Valid? (t_verify_step vs x));        
        lemma_t_verify_step_valid_implies_log_exists vs x;
        let Some entry = logS_to_logK_entry vs x in 
        let res = I.IntExtend _ _ (I.interleave_empty_n (Seq.length ss0)) entry i in
        IL _ _ res
      )
      else (
        assert (Seq.equal (Seq.index ss i)
                          (SA.append1 (Seq.index ss0 i) x));    
        assert (Valid? (t_verify i (Seq.index ss i)));
        assert (snd (thread_log ss i) == Seq.index ss i);
        assert (SA.prefix (Seq.index ss i) (Seq.length (Seq.index ss i) - 1) `Seq.equal` (Seq.index ss0 i));
        let vs = t_verify i (Seq.index ss0 i) in
        assert (Valid? vs);
        assert (Valid? (t_verify_step vs x));
        lemma_t_verify_step_valid_implies_log_exists vs x;
        let Some entry = logS_to_logK_entry vs x in
        let res = I.IntExtend _ _ prefix entry i in
        IL _ _ res
      )

let lemma_forall_store_ismap_extend #vcfg (il:its_log vcfg) (i:I.seq_index il)
  : Lemma (requires (forall_store_ismap (I.prefix il i) /\ 
                     is_map (thread_store (thread_state_post il i))))
          (ensures (forall_store_ismap (I.prefix il (i + 1))))
  = let il_i = I.prefix il i in
    let il_i1 = I.prefix il (i + 1) in
    let aux (tid:valid_tid il_i1)
      : Lemma (is_map (thread_store (thread_state il_i1 tid)))
      = if tid = il_thread_id_of il i
        then assert (thread_state il_i1 tid == thread_state_post il i)
        else ( 
          I.lemma_prefix_snoc il i;
          assert (thread_state il_i1 tid == thread_state il_i tid);
          assert (is_map (thread_store (thread_state il_i tid)))
        )
        in
    Classical.forall_intro aux


let lemma_forall_vtls_rel_extend #vcfg (il:its_log vcfg) (i:I.seq_index il)
  : Lemma (requires (forall_vtls_rel (I.prefix il i) (I.prefix (ilogS_to_logK il) i) /\
                     vtls_rel (thread_state_post il i) 
                              (SpecTS.thread_state_post (ilogS_to_logK il) i)))
          (ensures (forall_vtls_rel (I.prefix il (i + 1)) (I.prefix (ilogS_to_logK il) (i + 1))))
  = let il_i = I.prefix il i in
    let il_k_i = I.prefix (ilogS_to_logK il) i in
    let il_i1 = I.prefix il (i + 1) in
    let il_k_i1 = I.prefix (ilogS_to_logK il) (i + 1) in
    let aux (tid:valid_tid il_i1)
      : Lemma (vtls_rel (thread_state il_i1 tid) (SpecTS.thread_state il_k_i1 tid))
      = if tid = il_thread_id_of il i
        then (
          assert (thread_state il_i1 tid == thread_state_post il i);
          assert (SpecTS.thread_state il_k_i1 tid == SpecTS.thread_state_post (ilogS_to_logK il) i)
        )
        else (
          I.lemma_prefix_snoc il i;
          assert (thread_state il_i1 tid == thread_state il_i tid);
          I.lemma_prefix_snoc (ilogS_to_logK il) i;
          SpecTS.reveal_thread_state il_k_i tid;
          SpecTS.reveal_thread_state il_k_i1 tid;
          assert (SpecTS.thread_state il_k_i1 tid == SpecTS.thread_state il_k_i tid);
          assert (vtls_rel (thread_state il_i tid) (SpecTS.thread_state il_k_i tid))
        )
        in
    Classical.forall_intro aux

let lemma_forall_vtls_rel_implies_spec_verifiable #vcfg (il:its_log vcfg) (il':SpecTS.il_vlog)
  : Lemma (requires (forall_vtls_rel il il'))
          (ensures (SpecTS.verifiable il'))
          [SMTPat (forall_vtls_rel il il')]
  = let gl = g_logS_of il in
    let gl' = SpecTS.g_vlog_of il' in
    let aux (tid:seq_index gl') : Lemma (SpecT.verifiable (SpecG.thread_log gl' tid))
      = assert (tl_verifiable (thread_log gl tid));
        SpecTS.reveal_thread_state il' tid;
        assert (vtls_rel (thread_state il tid) (SpecTS.thread_state il' tid)) in
    Classical.forall_intro aux

let lemma_vtls_rel_and_clock_sorted_implies_spec_clock_sorted #vcfg (il:its_log vcfg) (i:I.seq_index il)
  : Lemma (requires (let il' = ilogS_to_logK il in
                     forall_vtls_rel (I.prefix il i) (I.prefix il' i)  /\
                     forall_vtls_rel (I.prefix il (i + 1)) (I.prefix il' (i + 1)) /\
                     SpecTS.clock_sorted (I.prefix il' i)))
          (ensures (let il' = ilogS_to_logK il in
                    SpecTS.clock_sorted (I.prefix il' (i + 1))))
  = let il_k = ilogS_to_logK il in
    let vs = thread_state_post il i in
    let vs' = SpecTS.thread_state_post il_k i in
    assert (Valid?.clock vs = Spec.Valid?.clk vs');
    let il_k_i = I.prefix il_k i in
    let il_k_i1 = I.prefix il_k (i + 1) in
    let aux (t1 t2:I.seq_index il_k_i1)
      : Lemma (requires t1 <= t2) 
              (ensures SpecTS.clock il_k_i1 t1 `ts_leq` SpecTS.clock il_k_i1 t2)
              [SMTPat(SpecTS.clock il_k_i1 t1 `ts_leq` SpecTS.clock il_k_i1 t2)]
      = //if t1 < i && t2 < i
        //then we should have (SpecTS.clock il_k_i1 = SpecTS.clock il_k_i), so the property holds by 
        //      our asumption that il_k_i is sorted
        // otherwise, we know that (il_clock il_i (i-1) = SpecTS.clock il_k_i (i-1)) and 
        //      (il_clock il_i1 i = SpecTS.clock il_k_i1 i), and il_i1 is sorted, which implies that 
        //      (SpecTS.clock il_k_i1 (i-1) `ts_leq` SpecTS.clock il_k_i1 i), so il_k_i1 is sorted
      admit() in
    ()


(* a union type that contains a hash collision or a proof of store_inv_rel_spec_eac for a specific itsl log *)
let store_inv_rel_spec_eac_or_hashcollision #vcfg (il:its_log vcfg) = 
  o:option hash_collision_gen{Some? o \/ store_inv_rel_spec_eac il}

let lemma_eac_boundary_inv (itsl: SpecTS.its_log) (i:I.seq_index itsl): 
  Lemma (requires (SpecTS.is_eac (I.prefix itsl i) /\
                   not (SpecTS.is_eac (I.prefix itsl (i + 1)))))
        (ensures (SpecTS.eac_boundary itsl = i)) = admit()

let lemma_store_rel_extend_addm #vcfg 
  (ils: il_hash_verifiable_log vcfg) 
  (i:I.seq_index ils {let ils_i = I.prefix ils i in
                      store_inv_rel_spec_eac ils_i /\
                      AddM_S? (I.index ils i)}):
  store_inv_rel_spec_eac_or_hashcollision (I.prefix ils (i + 1)) =     
  let ilk = ilogS_to_logK ils in  
  let ils_i = I.prefix ils i in
  let ilk_i = I.prefix ilk i in
  let ils_i1 = I.prefix ils (i + 1) in
  let ilk_i1 = I.prefix ilk (i + 1) in  

  (* thread id handling the i'th log entry *)
  let tid = il_thread_id_of ils i in
  // assert(SpecTS.thread_id_of ilk i = tid);

  let es = I.index ils i in
  let ek = I.index ilk i in

  lemma_ilogS_to_logK_prefix_commute ils i;
  // assert (ilk_i == ilogS_to_logK ils_i);
  
  lemma_ilogS_to_logK_prefix_commute ils (i + 1);
  // assert (ilk_i1 == ilogS_to_logK ils_i1);

  let vss_i = thread_state_pre ils i in
  lemma_forall_store_ismap_specialize ils i;
  // assert (is_map (thread_store vss_i));
  let vss_i1 = thread_state_post ils i in

  let vsk_i = SpecTS.thread_state_pre ilk i in 
  lemma_forall_vtls_rel_specialize ils i;
  // assert (vtls_rel vss_i vsk_i);
  let vsk_i1 = SpecTS.thread_state_post ilk i in

  lemma_verifier_thread_state_extend ils i;
  // assert (vss_i1 == t_verify_step vss_i es);

  SpecTS.lemma_verifier_thread_state_extend ilk i;
  assert (vsk_i1 == Spec.t_verify_step vsk_i ek);

  lemma_ilogS_to_logK_index ils i;
  // assert (ek == Some?.v (logS_to_logK_entry vss_i es));
  
  match es with
  | AddM_S s (k,v) s' ->  
    let sts = thread_store vss_i in
    let k' = stored_key sts s' in    
    assert(ek = Spec.AddM (k,v) k');    

    if store_contains_key sts k then (
      (* since the store contains k, the spec store also contains k, so the addm fails on spec *)
      // let stk = Spec.thread_store vsk_i in      
      // assert(Spec.store_contains stk k);
      
      assert(Spec.Failed? vsk_i1);
      assert(Spec.Failed == vsk_i1);

      (* ... this implies we need to show that addm fails in the intermediate level *)      
      (* the slot containing key k *)
      let sk = slot_of_key sts k in

      (* the add method of key k *)
      let amk = add_method_of sts sk in
      
      


      admit()
    )
    else (
      admit()
      (*
      // assert(not (store_contains_key sts k));
      lemma_vaddm_simulates_spec_if_k_is_new vss_i vsk_i s s' (k,v);
      lemma_forall_vtls_rel_extend ils i;
      lemma_vtls_rel_and_clock_sorted_implies_spec_clock_sorted ils i;
      let sts1 = thread_store vss_i1 in
      // assert(is_map sts1);
      lemma_forall_store_ismap_extend ils i;
      // assert(forall_store_ismap ils_i1);
      // assert(forall_vtls_rel ils_i1 ilk_i1);
      if SpecTS.is_eac ilk_i1 then None
      else (
        lemma_eac_boundary_inv ilk_i1 i;
        Some (lemma_non_eac_addm_implies_hash_collision ilk_i1)
      )*)
   )

let inductive_step #vcfg (ils: il_hash_verifiable_log vcfg) 
                   (i:I.seq_index ils {let ils_i = I.prefix ils i in
                                      store_inv_rel_spec_eac ils_i}):
  store_inv_rel_spec_eac_or_hashcollision (I.prefix ils (i + 1)) =     

  let es = I.index ils i in
  
  match es with
  | Get_S _ _ _ -> lemma_store_rel_extend_get ils i
  | Put_S _ _ _  -> lemma_store_rel_extend_put ils i
  | AddM_S _ _ _  -> lemma_store_rel_extend_addm ils i
  | _ -> admit()

(*
  


  




  let e = I.index il i in
  let e' = I.index il_k i in

  
  match e with
  
  | Get_S s k v ->
    lemma_vget_simulates_spec vs vs' s k v;
    lemma_forall_vtls_rel_extend il i;
    assert (forall_vtls_rel il_i1 il_k_i1);

    lemma_vtls_rel_and_clock_sorted_implies_spec_clock_sorted il i;
    assert (SpecTS.clock_sorted il_k_i1);

    if SpecTS.is_eac il_k_i1 then (
       lemma_vget_preserves_inv vs s k v;
       lemma_forall_store_inv_extend il i;
       assert (forall_store_inv il_i1);
       None
    )
    else (
      assume (Spec.Get? (SpecTS.eac_boundary_entry il_k_i1));
      Some (lemma_non_eac_get_implies_hash_collision il_k_i1)
    )

  | Put_S s k v ->
    lemma_vput_simulates_spec vs vs' s k v;
    lemma_forall_vtls_rel_extend il i;
    lemma_vtls_rel_and_clock_sorted_implies_spec_clock_sorted il i;

    if SpecTS.is_eac il_k_i1 then (
       lemma_vput_preserves_inv vs s k v; 
       lemma_forall_store_inv_extend il i;
       None
    )
    else ( 
      assume (Spec.Put? (SpecTS.eac_boundary_entry il_k_i1));
      Some (lemma_non_eac_put_implies_hash_collision il_k_i1)
    )

  | AddM_S s (k,v) s' ->
      if store_contains_key st k
      then (
        // We know that the log up to this point is EAC and the verifier state satisfies store_inv.
        // Based on this, we should be able to show that it is impossible for the vaddm
        // to successfully verify the current entry (contradicting our assumption that itsl is a 
        // hash verifiable log).
        // --> if k is in the store via MAdd, then the in_store bit must be set by store_inv
        // --> if k is in the store via BAdd, then the evicted_to_blum bit must be set by EAC
        admit()
      )
      else (
        let k' = stored_key st s' in
        lemma_vaddm_simulates_spec_if_k_is_new vs vs' s s' (k,v) k';
        lemma_forall_vtls_rel_extend il i;
        lemma_vtls_rel_and_clock_sorted_implies_spec_clock_sorted il i;

        if SpecTS.is_eac il_k_i1 then (
          
          // The following should hold from eac -- right? @Arvind
          assume(no_other_slot_points_to st s' k);
          assume(other_dir_does_not_point_to st s' (desc_dir k k') k);
          assume(valid_new_value st k v);

          lemma_vaddm_preserves_inv_if_k_is_new vs s s' (k,v); 
          lemma_forall_store_inv_extend il i;        
          None
        )
        else ( 
          assume (Spec.AddM? (SpecTS.eac_boundary_entry il_k_i1));
          Some (lemma_non_eac_addm_implies_hash_collision il_k_i1)      
        )
      )
  
  | EvictM_S s s' ->
      let k = stored_key st s in
      let k' = stored_key st s' in
      lemma_vevictm_simulates_spec vs vs' s s' k k';
      lemma_forall_vtls_rel_extend il i;
      lemma_vtls_rel_and_clock_sorted_implies_spec_clock_sorted il i;

      if SpecTS.is_eac il_k_i1 then (
      
        // The following should hold from eac -- right? @Arvind
        assume (pointed_key st s' (desc_dir k k') = k);
        assume(no_other_slot_points_to st s' k);
        assume(other_dir_does_not_point_to st s' (desc_dir k k') k);

        lemma_vevictm_preserves_inv vs s s'; 
        lemma_forall_store_inv_extend il i;        
        None
      )
      else ( 
        assume (Spec.EvictM? (SpecTS.eac_boundary_entry il_k_i1));
        Some (lemma_non_eac_evictm_implies_hash_collision il_k_i1)      
      )

  | AddB_S s (k,v) t j ->
      if store_contains_key st k
      then (
        // In this case, the add should produce a hash collision
        admit()
      )
      else (
        lemma_vaddb_simulates_spec_if_k_is_new vs vs' s (k,v) t j;
        lemma_forall_vtls_rel_extend il i;
        lemma_vtls_rel_and_clock_sorted_implies_spec_clock_sorted il i;

        if SpecTS.is_eac il_k_i1 then (
          
          // The following should hold from eac -- right? @Arvind
          assume(valid_new_value st k v);

          lemma_vaddb_preserves_inv_if_k_is_new vs s (k,v) t j; 
          lemma_forall_store_inv_extend il i;        
          None
        )
        else ( 
          // We can't use lemmas from Veritas.Verifier.EAC in this case because il_k is not hash verifiable
          admit()
        )
      )

  | EvictB_S s t ->
      let k = stored_key st s in
      lemma_vevictb_simulates_spec vs vs' s k t;
      lemma_forall_vtls_rel_extend il i;
      lemma_vtls_rel_and_clock_sorted_implies_spec_clock_sorted il i;

      if SpecTS.is_eac il_k_i1 then (
        lemma_vevictb_preserves_inv vs s t; 
        lemma_forall_store_inv_extend il i;        
        None
      )
      else ( 
        assume (Spec.EvictB? (SpecTS.eac_boundary_entry il_k_i1));
        Some (lemma_non_eac_evictb_implies_hash_collision il_k_i1)      
      )

  | EvictBM_S s s' t ->
      let k = stored_key st s in
      let k' = stored_key st s' in
      lemma_vevictbm_simulates_spec vs vs' s s' k k' t;
      lemma_forall_vtls_rel_extend il i;
      lemma_vtls_rel_and_clock_sorted_implies_spec_clock_sorted il i;

      if SpecTS.is_eac il_k_i1 then (
      
        // Will need some eac assumptions here
        
        lemma_vevictbm_preserves_inv vs s s' t; 
        lemma_forall_store_inv_extend il i;        
        None
      )
      else ( 
        assume (Spec.EvictBM? (SpecTS.eac_boundary_entry il_k_i1));
        Some (lemma_non_eac_evictbm_implies_hash_collision il_k_i1)      
      )
*)

(* empty log satisfies all invariants *)
let lemma_empty_store_inv_spec_rel #vcfg (itsl: its_log vcfg)
  : Lemma (requires (I.length itsl = 0))
          (ensures (store_inv_rel_spec_eac itsl)) 
  = admit()

let rec lemma_il_hash_verifiable_implies_eac_and_vtls_rel_aux 
      #vcfg
      (itsl:il_hash_verifiable_log vcfg) 
      (i:nat{i <= I.length itsl}) 
  : Tot (store_inv_rel_spec_eac_or_hashcollision (I.prefix itsl i))
    (decreases i)                 
  = let itsl_i = I.prefix itsl i in     
    if i = 0 then (
      lemma_empty_store_inv_spec_rel itsl_i;
      None
    )
    else 
      let hc_or_inv = lemma_il_hash_verifiable_implies_eac_and_vtls_rel_aux itsl (i - 1) in

      (* we found a hash collision - simply return the same *)
      if Some? hc_or_inv then
        Some (Some?.v hc_or_inv)
      else 
        // assert(store_inv_rel_spec_eac_or_hashcollision itsl_i');
        inductive_step itsl (i - 1)      
    
let lemma_il_hash_verifiable_implies_eac_and_vtls_rel #vcfg (il: il_hash_verifiable_log vcfg)
  : store_inv_rel_spec_eac_or_hashcollision il     
  = I.lemma_fullprefix_equal il;
    lemma_il_hash_verifiable_implies_eac_and_vtls_rel_aux il (I.length il)

let rec hadd_hevict_equal_aux #vcfg (gl:gl_verifiable_log vcfg) (gl':SpecG.verifiable_log) 
  : Lemma (requires Seq.length gl = Seq.length gl' /\
                    (forall (tid:seq_index gl). 
                       vtls_rel (verify (thread_log gl tid)) 
                                (SpecT.verify (SpecG.thread_log gl' tid))))
          (ensures hadd gl = SpecG.hadd gl' /\ hevict gl = SpecG.hevict gl')
          (decreases (Seq.length gl))
  = let n = Seq.length gl in
    if n <> 0
    then ( 
      let glp = prefix gl (n - 1) in
      let glp' = prefix gl' (n - 1) in
      let aux (tid:seq_index glp)
        : Lemma (vtls_rel (verify (thread_log glp tid)) 
                          (SpecT.verify (SpecG.thread_log glp' tid)))
        = assert (vtls_rel (verify (thread_log gl tid)) 
                           (SpecT.verify (SpecG.thread_log gl' tid))) in
      Classical.forall_intro aux;
      hadd_hevict_equal_aux glp glp'
    )

let lemma_forall_vtls_rel_implies_spec_hash_verifiable #vcfg (il:il_hash_verifiable_log vcfg) (il':SpecTS.its_log)
  : Lemma (requires forall_vtls_rel il il')
          (ensures SpecTS.hash_verifiable il')
  = let gl = g_logS_of il in
    let gl' = SpecTS.g_vlog_of il' in
    let aux (tid:seq_index gl) 
      : Lemma (vtls_rel (verify (thread_log gl tid))
                        (SpecT.verify (SpecG.thread_log gl' tid)))
      = SpecTS.reveal_thread_state il' tid in
    Classical.forall_intro aux;
    hadd_hevict_equal_aux gl gl'

*)

