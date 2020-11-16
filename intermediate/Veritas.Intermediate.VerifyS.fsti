module Veritas.Intermediate.VerifyS

open Veritas.Intermediate.Logs
open Veritas.Intermediate.StoreS

open Veritas.BinTree
open Veritas.Hash
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.MultiSetHashDomain
open Veritas.Record
open Veritas.SeqAux

module Spec = Veritas.Verifier
module SC = Veritas.Intermediate.VerifySC
module SCstore = Veritas.Intermediate.StoreSC

(* Thread-local state
   id     : thread id
   st     : thread local store
   clock  : current timestamp
   hadd   : add set hash
   hevict : evict set hash *)
noeq
type vtls =
  | Failed : vtls
  | Valid :
    id : thread_id ->
    st : vstore ->
    clock : timestamp ->
    hadd : ms_hash_value -> // TODO: should be a multiset
    hevict : ms_hash_value -> // TODO: should be a (multi?)set
    vtls

let thread_id_of (vs:vtls {Valid? vs}): thread_id = 
  Valid?.id vs

let thread_store (vs: vtls {Valid? vs}): vstore =
  Valid?.st vs

let thread_store_size (vs: vtls {Valid? vs}): nat =
  let st = thread_store vs in Seq.length st

let update_thread_store (vs:vtls {Valid? vs}) (st:vstore) : vtls =
  match vs with
  | Valid id _ clock hadd hevict -> Valid id st clock hadd hevict

let thread_clock (vs:vtls {Valid? vs}) = 
  Valid?.clock vs

let update_thread_clock (vs:vtls {Valid? vs}) (clock:timestamp): vtls = 
  match vs with
  | Valid id st _ hadd hevict -> Valid id st clock hadd hevict

let thread_hadd (vs:vtls {Valid? vs}) = 
  Valid?.hadd vs

let thread_hevict (vs:vtls {Valid? vs}) = 
  Valid?.hevict vs

let update_thread_hadd (vs:vtls {Valid? vs}) (hadd: ms_hash_value): vtls = 
  match vs with
  | Valid id st clock _ hevict -> Valid id st clock hadd hevict

let update_thread_hevict (vs:vtls {Valid? vs}) (hevict:ms_hash_value): vtls = 
  match vs with
  | Valid id st clock hadd _ -> Valid id st clock hadd hevict

let vget (s:slot_id) (k:key) (v:data_value) (vs: vtls {Valid? vs}) : vtls =
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (store_contains st s) then Failed
  (* check stored key and value *)
  else let k' = stored_key st s in
       let v' = stored_value st s in
       if k <> k' then Failed
       else if not (DVal? v') then Failed
       else if to_data_value v' <> v then Failed
       else vs

let vput (s:slot_id) (k:key) (v:data_value) (vs: vtls {Valid? vs}) : vtls =
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (store_contains st s) then Failed
  (* check stored key is k *)
  else let k' = stored_key st s in
       if k <> k' then Failed
       else if not (is_data_key (stored_key st s)) then Failed
       else update_thread_store vs (update_value st s (DVal v))

let vaddm (s:slot_id) (r:record) (s':slot_id) (vs: vtls {Valid? vs}): vtls =
  if not (s < thread_store_size vs) then Failed
  else 
    let st = thread_store vs in
    let (k,v) = r in
    (* check store contains slot s' *)
    if not (store_contains st s') then Failed
    else
      let k' = stored_key st s' in
      let v' = stored_value st s' in
      (* check k is a proper desc of k' *)
      if not (is_proper_desc k k') then Failed
      (* check store does not contain slot s *)
      else if store_contains st s then Failed
      (* check type of v is consistent with k *)
      else if not (is_value_of k v) then Failed
      (* check v' is a merkle value *)
      else if DVal? v' then Failed 
      else
        let v' = to_merkle_value v' in
        let d = desc_dir k k' in
        let dh' = desc_hash_dir v' d in 
        let h = hashfn v in
        match dh' with
        | Empty -> (* k' has no child in direction d *)
            (* first add must be init value *)
            if v <> init_value k then Failed
            else
              let v'_upd = Spec.update_merkle_value v' d k h false in
              let st_upd = update_value st s' (MVal v'_upd) in
              let st_upd2 = add_to_store st_upd s k v Spec.MAdd in
              let st_upd3 = update_in_store st_upd2 s' d true in
              update_thread_store vs st_upd3
        | Desc k2 h2 b2 -> 
            if k2 = k 
            then (* k is a child of k' *)
              (* check hashes match and k was not evicted to blum *)
              if not (h2 = h && b2 = false) then Failed
              (* check store does not contain k*)
              else if Left? d && l_child_in_store st s' then Failed
              else if Right? d && r_child_in_store st s' then Failed
              else 
                let st_upd = add_to_store st s k v Spec.MAdd in
                let st_upd2 = update_in_store st_upd s' d true in
                update_thread_store vs st_upd2
            else (* otherwise, k is not a child of k' *)
            (* first add must be init value *)
            if v <> init_value k then Failed
            (* check k2 is a proper desc of k *)
            else if not (is_proper_desc k2 k) then Failed
            else
              let d2 = desc_dir k2 k in
              let mv = to_merkle_value v in
              let mv_upd = Spec.update_merkle_value mv d2 k2 h2 b2 in
              let v'_upd = Spec.update_merkle_value v' d k h false in
              let st_upd = update_value st s' (MVal v'_upd) in
              let st_upd2 = add_to_store st_upd s k (MVal mv_upd) Spec.MAdd in
              let st_upd3 = update_in_store st_upd2 s' d true in
              let st_upd4 = update_in_store st_upd3 s d2 true in
              update_thread_store vs st_upd4

let has_instore_merkle_desc (st:vstore) (s:slot_id{store_contains st s}): bool = 
  let k = stored_key st s in
  if is_data_key k then false
  else 
    // TODO: remove the assert with a better SMTPat for stored_value_matches_stored_key
    let _ = assert (is_value_of k (stored_value st s)) in   
    let v = to_merkle_value (stored_value st s) in
    let ld = desc_hash_dir v Left in
    let rd = desc_hash_dir v Right in
    Desc? ld && l_child_in_store st s || 
    Desc? rd && r_child_in_store st s

let vevictm (s:slot_id) (s':slot_id) (vs: vtls {Valid? vs}): vtls = 
  let st = thread_store vs in
  (* check store contains s and s' *)
  if not (store_contains st s && store_contains st s') then Failed
  else 
    let k = stored_key st s in
    let v = stored_value st s in
    let k' = stored_key st s' in
    let v' = stored_value st s' in
    (* check k is a proper descendent of k' *)
    if not (is_proper_desc k k') then Failed
    (* check k does not have a child in the store *)
    else if has_instore_merkle_desc st s then Failed
    else
      let d = desc_dir k k' in
      // TODO: remove the assert with a better SMTPat for stored_value_matches_stored_key
      let _ = assert (is_value_of k' v') in 
      let v' = to_merkle_value v' in
      let dh' = desc_hash_dir v' d in
      let h = hashfn v in
      match dh' with
      | Empty -> Failed
      | Desc k2 h2 b2 -> 
          if k2 <> k then Failed
          else
            let v'_upd = Spec.update_merkle_value v' d k h false in
            let st_upd = update_value st s' (MVal v'_upd) in
            let st_upd2 = evict_from_store st_upd s in
            update_thread_store vs st_upd2

let vaddb (s:slot_id) (r:record) (t:timestamp) (j:thread_id) (vs:vtls {Valid? vs}): vtls = 
  if not (s < thread_store_size vs) then Failed
  else
    let st = thread_store vs in 
    let (k,v) = r in
    (* check value type consistent with key k *)
    if not (is_value_of k v) then Failed
    (* check store contains slot s *)
    else if store_contains st s then Failed
    else 
      (* update add hash *)
      let h = thread_hadd vs in
      let h_upd = ms_hashfn_upd (MHDom (k,v) t j) h in
      let vs_upd = update_thread_hadd vs h_upd in
      (* update clock *)
      let clk = thread_clock vs in
      let clk_upd = Spec.max clk (next t) in
      let vs_upd2 = update_thread_clock vs_upd clk_upd in
      (* add record to store *)
      let st_upd = add_to_store st s k v Spec.BAdd in
      update_thread_store vs_upd2 st_upd

let vevictb (s:slot_id) (t:timestamp) (vs:vtls {Valid? vs}): vtls = 
  let clock = thread_clock vs in
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (store_contains st s) then Failed
  else
    let k = stored_key st s in
    let v = stored_value st s in
    (* check key at s is not root *)
    if k = Root then Failed
    (* check time of evict < current time *)
    else if not (ts_lt clock t) then Failed
    (* check s was added through blum *)  
    else if add_method_of st s <> Spec.BAdd then Failed
    (* check k has no children n the store *)
    else if has_instore_merkle_desc st s then Failed  
    else 
      (* update evict hash *)
      let h = thread_hevict vs in
      let h_upd = ms_hashfn_upd (MHDom (k,v) t (thread_id_of vs)) h in
      let vs_upd = update_thread_hevict vs h_upd in
      (* update clock *)
      let vs_upd2 = update_thread_clock vs_upd t in    
      (* evict record *)
      let st_upd = evict_from_store st s in
      update_thread_store vs_upd2 st_upd

let vevictbm (s:slot_id) (s':slot_id) (t:timestamp) (vs:vtls {Valid? vs}): vtls = 
  let st = thread_store vs in
  (* check store contains s and s' *)
  if not (store_contains st s && store_contains st s') then Failed
  else
    let k = stored_key st s in
    let k' = stored_key st s' in
    let v' = stored_value st s' in
    (* check k is a proper desc of k' *)
    if not (is_proper_desc k k') then Failed
    (* check s was added through merkle *)
    else if add_method_of st s <> Spec.MAdd then Failed  
    (* check k has no children in the store *)
    else if has_instore_merkle_desc st s then Failed  
    else
      // TODO: remove the assert with a better SMTPat for stored_value_matches_stored_key
      let _ = assert (is_value_of k' v') in 
      let v' = to_merkle_value v' in
      let d = desc_dir k k' in
      let dh' = desc_hash_dir v' d in
      match dh' with
      | Empty -> Failed
      | Desc k2 h2 b2 -> 
          if k2 <> k || b2 then Failed
          else
            let v'_upd = Spec.update_merkle_value v' d k h2 true in
            let st_upd = update_value st s' (MVal v'_upd) in
            vevictb s t (update_thread_store vs st_upd)

(* Relation between SC and S thread-local states *)

let hashes_diverged (hadd:ms_hash_value) (hevict:ms_hash_value) : bool = 
  // TODO: informally, there is no way to extend the add or evict sets so that their hashes match
  admit()
  
let vtls_rel (vs:vtls) (vs':SC.vtls) : Type =
  (Failed? vs /\ SC.Failed? vs') \/
  (Valid? vs /\ SC.Valid? vs' /\
   (let (Valid id st clk ha he) = vs in
    let (SC.Valid id' st' clk' ha' he') = vs' in
    // all fields are equal
    equal_contents st st' /\ id = id' /\ clk = clk' /\ ha = ha' /\ he = he' /\
    // SC's is_map field indicates that the add/evict sets have diverged -- not needed?
    (not (SC.thread_store_is_map vs') ==> hashes_diverged ha he) /\
    // the invariant over MAdd keys always holds
    merkle_store_inv st /\ 
    // the invariant over BAdd keys holds if the add/evict sets have not diverged
    (not (hashes_diverged ha he) ==> blum_store_inv st)))

let lemma_vget_simulates_SC 
      (vs:vtls{Valid? vs})
      (vs':SC.vtls{SC.Valid? vs'})
      (s:slot_id)
      (k:data_key)
      (v:data_value)
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vget s k v vs) (SC.vget s k v vs')))
          // TODO: add a condition to each 'ensures' that says that the add/evict hashes stay diverged
  = ()

let lemma_update_value_DVal_preserves_merkle_inv (st:vstore) (s:slot_id{store_contains st s /\ is_data_key (stored_key st s)}) (v:data_value)
  : Lemma (requires merkle_store_inv st)
          (ensures merkle_store_inv (update_value st s (DVal v)))
          [SMTPat (merkle_store_inv (update_value st s (DVal v)))]
  = admit()

let lemma_update_value_DVal_preserves_blum_inv (st:vstore) (s:slot_id{store_contains st s /\ is_data_key (stored_key st s)}) (v:data_value)
  : Lemma (requires blum_store_inv st)
          (ensures blum_store_inv (update_value st s (DVal v)))
          [SMTPat (blum_store_inv (update_value st s (DVal v)))]
  = admit()

let lemma_vput_simulates_SC
      (vs:vtls{Valid? vs}) 
      (vs':SC.vtls{SC.Valid? vs'}) 
      (s:slot_id) 
      (k:data_key) 
      (v:data_value) 
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vput s k v vs) (SC.vput s k v vs'))) 
  = ()

let lemma_vaddm_simulates_SC 
      (vs:vtls{Valid? vs}) 
      (vs':SC.vtls{SC.Valid? vs'}) 
      (s s':slot_id)
      (r:record)  
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vaddm s r s' vs) (SC.vaddm s r s' vs'))) 
  = if s < thread_store_size vs
    then 
      let st = thread_store vs in
      let (k,v) = r in
      if store_contains st s'
      then
        let k' = stored_key st s' in
        let v' = stored_value st s' in
        if is_proper_desc k k' && not (store_contains st s) && not (DVal? v')
        then
          let v' = to_merkle_value v' in
          let d = desc_dir k k' in
          let dh' = desc_hash_dir v' d in 
          let h = hashfn v in
          let st' = SC.thread_store vs' in
          match dh' with
          | Empty -> 
              // CASE 1 - by points_to_nearest_desc_in_store, either k is not in the store or the evict/add sets have diverged
              if v = init_value k 
              then (
                let v'_upd = Spec.update_merkle_value v' d k h false in
                let st_upd = update_value st s' (MVal v'_upd) in
                let st_upd2 = add_to_store st_upd s k v Spec.MAdd in
                let st_upd3 = update_in_store st_upd2 s' d true in
                assume (merkle_store_inv st_upd3);
                if (hashes_diverged (thread_hadd vs) (thread_hevict vs))
                then (
                  let Valid _ st _ _ _ = update_thread_store vs st_upd3 in
                  assume (SC.Valid? (SC.vaddm s r s' vs'));
                  assume (not (SC.thread_store_is_map (SC.vaddm s r s' vs'))) 
                  )
                else (
                  assert (points_to_nearest_desc_in_store st s' Spec.BAdd);
                  assert (not (store_contains_key_with_am st k Spec.BAdd));
                  assert (not (store_contains_key_with_am st k Spec.MAdd));
                  assert (not (store_contains_key st k));
                  lemma_equal_contents_store_contains_key st st' k;
                  //assert (not (SCstore.store_contains_key st' k));
                  let Valid id st clk ha he = update_thread_store vs st_upd3 in
                  let SC.Valid id' st' clk' ha' he' = SC.vaddm s r s' vs' in
                  assume (blum_store_inv st); // easy since we are not adding anything via BAdd
                  admit()
                )
              )
          | Desc k2 h2 b2 -> 
              if k2 = k 
              // CASE 2 - by in_store_flag_implies... and evicted_to_blum_flag_implies..., either k is not in the store or the evict/add sets have diverged
              then admit()
              // CASE 3 - similar to CASE 1
              else admit()

let lemma_evict_from_store_preserves_merkle_inv (st:vstore) (s:slot_id{store_contains st s})
  : Lemma (requires merkle_store_inv st)
          (ensures merkle_store_inv (evict_from_store st s))
          [SMTPat (merkle_store_inv (evict_from_store st s))]
  = admit()

let lemma_update_evict_from_store_preserves_blum_inv (st:vstore) (s:slot_id{store_contains st s})
  : Lemma (requires blum_store_inv st)
          (ensures blum_store_inv (evict_from_store st s))
          [SMTPat (blum_store_inv (evict_from_store st s))]
  = admit()

let lemma_has_in_store_merkle_desc (st:vstore) (st':SCstore.vstore) (s:slot_id{store_contains st s})
  : Lemma (requires equal_contents st st' /\ merkle_store_inv st)
          (ensures has_instore_merkle_desc st s = SC.has_instore_merkle_desc st' (SCstore.stored_key st' s))
          [SMTPat (has_instore_merkle_desc st s); SMTPat (SC.has_instore_merkle_desc st' (SCstore.stored_key st' s))]
  = admit()

let lemma_vevictm_simulates_SC 
      (vs:vtls{Valid? vs}) 
      (vs':SC.vtls{SC.Valid? vs'}) 
      (s s':slot_id)  
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vevictm s s' vs) (SC.vevictm s s' vs'))) 
  = let st = thread_store vs in
    let st' = SC.thread_store vs' in
    if store_contains st s && store_contains st s'
    then 
      let k = stored_key st s in
      let v = stored_value st s in
      let k' = stored_key st s' in
      let v' = stored_value st s' in
      if is_proper_desc k k' && not (has_instore_merkle_desc st s) 
      then
        let d = desc_dir k k' in
        let _ = assert (is_value_of k' v') in 
        let v' = to_merkle_value v' in
        let dh' = desc_hash_dir v' d in
        let h = hashfn v in
        match dh' with
        | Empty -> ()
        | Desc k2 h2 b2 ->
            if k2 = k
            then
              let v'_upd = Spec.update_merkle_value v' d k h false in
              let st_upd = update_value st s' (MVal v'_upd) in
              let st_upd2 = evict_from_store st_upd s in
              let Valid id st clk ha he = update_thread_store vs st_upd2 in
              assume (merkle_store_inv st_upd);
              if not (hashes_diverged ha he) 
              then assume (blum_store_inv st_upd)

let lemma_vaddb_simulates_SC 
      (vs:vtls{Valid? vs}) 
      (vs':SC.vtls{SC.Valid? vs'}) 
      (s:slot_id)
      (r:record)
      (t:timestamp)
      (j:thread_id)
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vaddb s r t j vs) (SC.vaddb s r t j vs')))
  = if s < thread_store_size vs
    then
      let st = thread_store vs in 
      let (k,v) = r in
      if is_value_of k v
      then if not (store_contains st s)
      then
        let h = thread_hadd vs in
        let h_upd = ms_hashfn_upd (MHDom (k,v) t j) h in
        let vs_upd = update_thread_hadd vs h_upd in
        let clk = thread_clock vs in
        let clk_upd = Spec.max clk (next t) in
        let vs_upd2 = update_thread_clock vs_upd clk_upd in
        let st_upd = add_to_store st s k v Spec.BAdd in
        let Valid _ st _ ha he = update_thread_store vs_upd2 st_upd in
        assume (merkle_store_inv st); // easy since we are not adding anything via MAdd
        assume (not (SC.thread_store_is_map (SC.vaddb s r t j vs')) ==> hashes_diverged ha he);  
        assume (not (hashes_diverged ha he) ==> blum_store_inv st)

(* Thoughts on filling in the last two assumes:

   if store_contains_key k
   then (
     the SC is_map flag will be false
     hashes_diverged should be true
     -> blum_store_inv st does not need to hold
   )
   else (
     SC will leave the is_map flag unchanged
     if blum_store_inv is violated by adding k
     then (
       there exists a slot s s.t.
       (a) k is marked as a descendent of s and the evicted_to_blum flag of s is not set 
       or (b) k is a descendent of s, but is not stored in the hash of s

       ... in either case, the hashes have diverged
     )
     -> this proves (not hashes_diverged ==> blum_store_inv holds)
   )
*)

let lemma_vevictb_simulates_SC 
      (vs:vtls{Valid? vs}) 
      (vs':SC.vtls{SC.Valid? vs'}) 
      (s:slot_id)
      (t:timestamp)
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vevictb s t vs) (SC.vevictb s t vs'))) 
  = let clock = thread_clock vs in
    let st = thread_store vs in
    if store_contains st s 
    then
      let k = stored_key st s in
      let v = stored_value st s in
      if k <> Root && ts_lt clock t && add_method_of st s = Spec.BAdd && not (has_instore_merkle_desc st s)
      then
        let h = thread_hevict vs in
        let h_upd = ms_hashfn_upd (MHDom (k,v) t (thread_id_of vs)) h in
        let vs_upd = update_thread_hevict vs h_upd in
        let vs_upd2 = update_thread_clock vs_upd t in    
        let st_upd = evict_from_store st s in
        let Valid _ _ _ ha he = update_thread_store vs_upd2 st_upd in
        if (hashes_diverged ha he) then assume (blum_store_inv st)

let lemma_vevictbm_simulates_SC 
      (vs:vtls{Valid? vs}) 
      (vs':SC.vtls{SC.Valid? vs'}) 
      (s s':slot_id)
      (t:timestamp)
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vevictbm s s' t vs) (SC.vevictbm s s' t vs'))) 
  = let st = thread_store vs in
    if store_contains st s && store_contains st s' 
    then
      let k = stored_key st s in
      let k' = stored_key st s' in
      let v' = stored_value st s' in
      if is_proper_desc k k' && add_method_of st s = Spec.MAdd && not (has_instore_merkle_desc st s)
      then
        let _ = assert (is_value_of k' v') in 
        let v' = to_merkle_value v' in
        let d = desc_dir k k' in
        let dh' = desc_hash_dir v' d in
        match dh' with
        | Empty -> ()
        | Desc k2 h2 b2 -> 
            if k2 = k && not b2 
            then (
              let v'_upd = Spec.update_merkle_value v' d k h2 true in
              let st_upd = update_value st s' (MVal v'_upd) in
              let st' = SC.thread_store vs' in
              let st_upd' = SCstore.update_store st' s' (MVal v'_upd) in
              let Valid id st clk ha he = update_thread_store vs st_upd in
              assume (merkle_store_inv st_upd); // same assumes as vevictm
              if not (hashes_diverged ha he) 
              then assume (blum_store_inv st_upd);
              lemma_vevictb_simulates_SC (update_thread_store vs st_upd) (SC.update_thread_store vs' st_upd') s t
            )

let t_verify_step (vs:vtls) (e:logS_entry): vtls =
  match vs with
  | Failed -> Failed
  | _ ->
    match e with
    | Get_S s k v -> vget s k v vs
    | Put_S s k v -> vput s k v vs
    | AddM_S s r s' -> vaddm s r s' vs
    | EvictM_S s s' -> vevictm s s' vs
    | AddB_S s r t j -> vaddb s r t j vs
    | EvictB_S s t -> vevictb s t vs
    | EvictBM_S s s' t -> vevictbm s s' t vs

(* Verify a log from a specified initial state *)
let rec t_verify_aux (vs:vtls) (l:logS): Tot vtls
  (decreases (Seq.length l)) =
  let n = Seq.length l in
  if n = 0 then vs
  else
    let lp = prefix l (n - 1) in
    let vsp = t_verify_aux vs lp in
    let e = Seq.index l (n - 1) in
    t_verify_step vsp e

// ... 
