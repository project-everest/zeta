module Zeta.Intermediate.Verifier

#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 2 --query_stats"

let vaddm #vcfg (r:record vcfg.app) (s:slot_id vcfg)  (s':slot_id vcfg) (vs: vtls_t vcfg {vs.valid}):
  (vs': vtls_t vcfg {let a = AMP s r s' vs in
                   addm_precond a /\ addm_postcond a vs' \/
                   ~(addm_precond a) /\ ~vs'.valid}) =
  let a = AMP s r s' vs in
  let st = vs.st in
  let (gk,gv) = r in
  let k = to_base_key gk in
  if s = s' then fail vs
  (* check slot s' is not empty *)
  else if empty_slot st s' then fail vs
  else
    let k' = stored_base_key st s' in
    let v' = stored_value st s' in
    (* check k is a proper desc of k' *)
    if not (is_proper_desc k k') then fail vs
    (* check slot s is empty *)
    else if inuse_slot st s then fail vs
    (* check type of v is consistent with k *)
    else
      let v' = to_merkle_value v' in
      let d = desc_dir k k' in
      let dh' = desc_hash v' d in
      let h = hashfn gv in
      match dh' with
      | Empty -> (* k' has no child in direction d *)
        if not (is_init_record r) then fail vs
        else if points_to_some_slot st s' d then fail vs
        else
          let st = madd_to_store st s r s' d in
          let v' = Merkle.update_value v' d k Zeta.Hash.zero false in
          let st = update_value st s' (IntV v') in
          update_thread_store vs st
      | Desc k2 h2 b2 ->
        if k2 = k then (* k is a child of k' *)
          if not (h2 = h && b2 = false) then fail vs
          (* check slot s' does not contain a desc along direction d *)
          else if points_to_some_slot st s' d then fail vs
          else
            let st = madd_to_store st s r s' d in
            update_thread_store vs st
        else (* otherwise, k is not a child of k' *)
          (* first add must be init value *)
          if not (is_init_record r) then fail vs
          (* check k2 is a proper desc of k *)
          else if not (is_proper_desc k2 k) then fail vs
          else
            let d2 = desc_dir k2 k in
            let mv = to_merkle_value gv in
            let mv = Merkle.update_value mv d2 k2 h2 b2 in
            let v' = Merkle.update_value v' d k Zeta.Hash.zero false in
            let st =  if points_to_some_slot st s' d then
                        madd_to_store_split st s (gk, (IntV mv)) s' d d2
                      else
                        madd_to_store st s (gk, (IntV mv)) s' d in
            let st = update_value st s' (IntV v') in
            update_thread_store vs st

#pop-options
