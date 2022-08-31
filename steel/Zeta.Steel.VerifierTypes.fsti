module Zeta.Steel.VerifierTypes

open Zeta.Steel.ApplicationTypes
open Zeta.Steel.FormatsManual
open Steel.ST.Util
module M = Zeta.Steel.ThreadStateModel

#push-options "--ide_id_info_off"

[@@CAbstractStruct]
val thread_state_t
  : Type0

val thread_id (t:thread_state_t)
  : tid

val thread_state_inv_core (t:thread_state_t)
                          ([@@@smt_fallback] m:M.thread_state_model)
  : vprop

let tsm_entries_invariant (tsm:M.thread_state_model) =
    not tsm.failed ==>
    tsm == M.verify_model (M.init_thread_state_model tsm.thread_id)
                          tsm.processed_entries

val thread_state_inv (t:thread_state_t)
                     ([@@@smt_fallback] m:M.thread_state_model)
  : vprop

val intro_thread_state_inv (#o:_)
                           (#tsm:M.thread_state_model)
                           (t:thread_state_t)
  : STGhost unit o
    (thread_state_inv_core t tsm)
    (fun _ -> thread_state_inv t tsm)
    (requires
      thread_id t == tsm.thread_id /\
      tsm_entries_invariant tsm)
    (ensures fun _ -> True)

val elim_thread_state_inv (#o:_) (#tsm:M.thread_state_model) (t:thread_state_t)
  : STGhost unit o
    (thread_state_inv t tsm)
    (fun _ -> thread_state_inv_core t tsm)
    (requires True)
    (ensures fun _ ->
      thread_id t == tsm.thread_id /\
      tsm_entries_invariant tsm)

let extract_tsm_entries_invariant (#o:_) (#tsm:M.thread_state_model) (t:thread_state_t)
  : STGhost unit o
    (thread_state_inv t tsm)
    (fun _ -> thread_state_inv t tsm)
    (requires True)
    (ensures fun _ ->
      thread_id t == tsm.thread_id /\
      tsm_entries_invariant tsm)
  = elim_thread_state_inv t;
    intro_thread_state_inv t

noeq
type kv = {
     key:key;
     value:(v:value {is_value_of key v})
}

module U16 = FStar.UInt16
inline_for_extraction
let read_store_t =
    #tsm:M.thread_state_model ->
    t:thread_state_t ->
    slot:slot ->
    ST (option kv)
       (thread_state_inv_core t tsm)
       (fun _ -> thread_state_inv_core t tsm)
       (requires True)
       (ensures fun o ->
         match Seq.index tsm.store (U16.v slot), o with
         | None, None -> True
         | Some (se : M.store_entry), Some kv -> se.key == kv.key /\ se.value == kv.value
         | _ -> False)


let value_compat_with_slot (tsm:M.thread_state_model) (slot:slot) (v:value)
  : prop
  = match Seq.index tsm.store (U16.v slot) with
    | None -> False
    | Some (se : M.store_entry) -> is_value_of se.key v == true

let update_tsm_slot_value (tsm:M.thread_state_model) (slot:slot) (v:value { value_compat_with_slot tsm slot v })
  : GTot M.thread_state_model
  = let Some se = Seq.index tsm.store (U16.v slot) in
    let se' = { se with value = v } in
    let store' = Seq.upd tsm.store (U16.v slot) (Some se') in
    { tsm with store = store' }

inline_for_extraction
let write_store_t =
    #tsm:M.thread_state_model ->
    t:thread_state_t ->
    slot:slot ->
    v:value { value_compat_with_slot tsm slot v } ->
    STT unit
       (thread_state_inv_core t tsm)
       (fun _ -> thread_state_inv_core t (update_tsm_slot_value tsm slot v))

inline_for_extraction
val read_store : read_store_t

inline_for_extraction
val write_store : write_store_t


//
// Wrapper over read_store,
//   with additional check that the slot contains application key and value
//
inline_for_extraction
let read_store_app (#tsm:M.thread_state_model)
  (t:thread_state_t)
  (slot:slot)
  : ST (option (key_type & option value_type))
       (thread_state_inv_core t tsm)
       (fun _ -> thread_state_inv_core t tsm)
       (requires True)
       (ensures fun o ->
        match Seq.index tsm.store (U16.v slot), o with
        | Some (se:M.store_entry), Some (k, vopt) ->
          se.key == ApplicationKey k /\ se.value == DValue vopt
        | _, None -> True
        | _, _ -> False)

  = let kvopt = read_store t slot in
    match kvopt with
    | Some ({key=ApplicationKey k; value=DValue vopt}) -> Some (k, vopt)
    | _ -> None

//
// Used by app function implementations
//
val restore_thread_state_inv_app (#opened:_) (#tsm:M.thread_state_model)
  (t:thread_state_t)
  (app_results:M.app_results)
  (processed_entries:Seq.seq log_entry)
  : STGhost unit opened
      (thread_state_inv_core t tsm)
      (fun _ -> thread_state_inv t ({tsm with app_results; processed_entries}))
      (requires
        thread_id t == tsm.thread_id /\
        M.tsm_entries_invariant ({tsm with app_results; processed_entries}))
      (ensures fun _ -> True)
