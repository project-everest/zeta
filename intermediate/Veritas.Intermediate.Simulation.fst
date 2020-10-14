module Veritas.Intermediate.Simulation

module Spec = Veritas.Verifier
module IC = Veritas.Intermediate.Common
module IS = Veritas.Intermediate.Store
module IV = Veritas.Intermediate.Verifier

(* Relation between stores *)
let store_rel (st:IS.vstore) (st':Spec.vstore) : Type = 
  // no duplicates in st
  (forall (s:IC.slot_id{IS.contains_record st s}) 
     (s':IC.slot_id{IS.contains_record st s'}).
     IS.get_key_at st s <> IS.get_key_at st s') /\
  // values is st and st' match -- do we need both directions?
  (forall (s:IC.slot_id{IS.contains_record st s}).
     let k = IS.get_key_at st s in 
     let v = IS.get_value_at st s in
     let a = IS.get_add_method_at st s in
     Spec.store_contains st' k /\ 
     v = Spec.stored_value st' k /\
     a = Spec.add_method_of st' k) /\
  (forall (k:Veritas.Key.key{Spec.store_contains st' k}). 
     let v' = Spec.stored_value st' k in
     let a' = Spec.add_method_of st' k in
     IS.contains_key st k /\
     v' = IS.value_of st k /\
     a' = IS.add_method_of st k)

(* Relation between thread-local states *)
let vtls_rel (vs:IV.vtls) (vs':Spec.vtls) : Type =
  // either both runs failed
  (IV.Failed? vs /\ Spec.Failed? vs') \/
  // or vs is not a valid map (which relates to any vs')
  (IV.Valid? vs /\ not (IV.thread_store_is_map vs)) \/
  // or vs and vs' have related stores
  (match vs, vs' with
   | IV.Valid id st clk ha he, Spec.Valid id' st' clk' _ ha' he' ->
       store_rel st st' /\ 
       // other fields related by equality -- may not need? 
       id = id' /\ clk = clk' /\ ha = ha' /\ he = he'   
   | _ -> False)

(* Relation between a key and slot id *)
let slot_key_rel (vs:IV.vtls) (s:IC.slot_id) (k:Veritas.Key.key) : Type =
  IV.Valid? vs /\ 
  (not (IV.thread_store_is_map vs) \/ 
    (let st = IV.Valid?.st vs in
     IS.contains_record st s && IS.get_key_at st s = k))

(* Simulation statement for vput *)
let lemma_vput_simulates_spec 
      (vs:IV.vtls) 
      (vs':Spec.vtls) 
      (s:IC.slot_id) 
      (k:Veritas.Key.data_key) 
      (v:Veritas.Record.data_value) 
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k
                     /\ Spec.Valid? vs' ))
          (ensures (vtls_rel (IV.vput s v vs) (Spec.vput k v vs'))) 
  = admit()

(* Relation between logs *)
let log_rel (l:IV.vlog) (l':Spec.vlog) : Type = 
  admit()

let lemma_t_verify_simulates_spec (id:IC.thread_id) (l:IV.vlog) (l':Spec.vlog)
  : Lemma (requires (log_rel l l'))
          (ensures (vtls_rel (IV.t_verify id l) (Spec.t_verify id l')))
  = admit()

(* End goal: For any log, the intermediate implementation will verify 
   iff the the spec implementation does. *)
module VT = Veritas.Verifier.Thread
let lemma_verifiable_simulates_spec (id:IC.thread_id) (l:IV.vlog) (l':Spec.vlog)
  : Lemma (requires (log_rel l l'))
          (ensures (let tl : VT.thread_id_vlog = (id,l') in
                    IV.verifiable id l = VT.verifiable tl))
  = lemma_t_verify_simulates_spec id l l';
    let vs = IV.t_verify id l in
    if IV.Valid? vs
    then if not (IV.thread_store_is_map vs) 
    then admit()
