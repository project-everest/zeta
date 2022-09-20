module Zeta.Steel.Application

open Steel.ST.Effect.Atomic

module U16 = FStar.UInt16

module App = Zeta.App

module TSM = Zeta.Steel.ThreadStateModel

module VT = Zeta.Steel.VerifierTypes

module AT = Zeta.Steel.ApplicationTypes
module S = Zeta.KeyValueStore.Spec
module F = Zeta.KeyValueStore.Formats

friend Zeta.Steel.ApplicationTypes

/// Implementation of the steel/Zeta.Steel.Application interface
///
/// Each app function implementation is staged
///   There is an impl function that implements the core functionality and optionally writes to the store
///   And there is a wrapper around this impl, that:
///     - parses the input log to read function arguments etc.
///     - reads the store for requested keys
///     - calls the impl function with the arguments and read store values,
///     - writes to the output log if needed

#set-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 64"


//
// This is the precondition of the impl functions
//
let slot_value_is_kv
  (tsm:TSM.thread_state_model)
  (slot:slot_id)
  (store_kv:AT.key_type & option AT.value_type)
  = U16.v slot < U16.v AT.store_size /\
    Some? (Seq.index tsm.store (U16.v slot)) /\
    (let Some se = Seq.index tsm.store (U16.v slot) in
     se.key == ApplicationKey (fst store_kv) /\
     se.value == DValue (snd store_kv))


/// Following are some helpers for each function,
///   we will use these ghostly to re-establish invariants

let vget_spec_args (r:F.vget_args_t)
  : GTot (App.interp_code S.adm S.vget_spec_arg_t)
  = r.vget_key, r.vget_value

let vget_spec_slots (r:F.vget_args_t)
  : GTot (Seq.seq slot_id)
  = Seq.create 1 r.vget_slot

let vget_spec_out_vals (tsm:TSM.thread_state_model) (r:F.vget_args_t)
  : Ghost (r:Seq.seq (App.app_value_nullable S.adm){Seq.length r == S.vget_spec_arity})
          (requires Some? (TSM.read_slots tsm (vget_spec_slots r)))
          (ensures fun _ -> True)
  = let recs = Some?.v (TSM.read_slots tsm (vget_spec_slots r)) in
    let _, _, out_vals = S.vget_spec_f (vget_spec_args r) recs in
    out_vals

let vget_app_result (tsm:TSM.thread_state_model) (r:F.vget_args_t)
  : Ghost app_result_entry
      (requires Some? (TSM.read_slots tsm (vget_spec_slots r)))
      (ensures fun _ -> True)
  = let recs = Some?.v (TSM.read_slots tsm (vget_spec_slots r)) in
    let _, res, _ = S.vget_spec_f (vget_spec_args r) recs in  
    (| S.vget_id, vget_spec_args r, recs, res |)

let vget_app_success (tsm:TSM.thread_state_model) (r:F.vget_args_t)
  : Ghost bool
      (requires Some? (TSM.read_slots tsm (vget_spec_slots r)))
      (ensures fun _ -> True)
  = let recs = Some?.v (TSM.read_slots tsm (vget_spec_slots r)) in
    let r, _, _ = S.vget_spec_f (vget_spec_args r) recs in
    App.Fn_success? r

//
// Pairwise comparison of all slots in the arg
//
inline_for_extraction
let vget_arg_slots_distinct (r:F.vget_args_t)
  : Pure bool
      (requires True)
      (ensures fun b -> b <==> Zeta.SeqAux.distinct_elems_comp (vget_spec_slots r))
  = true

//
// Pairwise comparison of slot keys
//
inline_for_extraction
let vget_keys_distinct (tsm:TSM.thread_state_model) (r:F.vget_args_t) (k:AT.key_type)
  : Pure bool
      (requires Some? (TSM.read_slots tsm (vget_spec_slots r)) /\
                (let kvs = Some?.v (TSM.read_slots tsm (vget_spec_slots r)) in
                 Seq.equal (Zeta.SeqAux.map fst kvs) (Seq.create 1 k)))
      (ensures fun b -> b <==> TSM.check_distinct_keys (Some?.v (TSM.read_slots tsm (vget_spec_slots r))))
  = true

//
// Final tsm for every app function impl (note impl)
// Differs from input tsm only in store (if at all)
//
// It is more interesting for vput
//
let vget_impl_tsm
  (tsm:TSM.thread_state_model)
  (r:F.vget_args_t)
  (store_kv:(F.key_t & option F.value_t){slot_value_is_kv tsm r.vget_slot store_kv})
  : TSM.thread_state_model
  = tsm

//
// The core vget implementation
//
// If it succeeds, it provides all the successful checks in its postcondition,
//
let vget_impl (#tsm:TSM.thread_state_model)
  (t:VT.thread_state_t)
  (r:F.vget_args_t)
  (store_kv:(F.key_t & option F.value_t){slot_value_is_kv tsm r.vget_slot store_kv})
  : ST bool
      (VT.thread_state_inv_core t tsm)
      (fun b -> 
       if b
       then VT.thread_state_inv_core t (vget_impl_tsm tsm r store_kv)
       else VT.thread_state_inv_core t tsm)
      (requires True)
      (ensures fun b ->
         (b ==> (r.vget_key == fst store_kv /\
                Some r.vget_value == snd store_kv /\
                Zeta.SeqAux.distinct_elems_comp (vget_spec_slots r) /\
                TSM.check_distinct_keys (Some?.v (TSM.read_slots tsm (vget_spec_slots r))) /\
                vget_app_success tsm r)))
  = //Check distinctness of keys and slots
    if vget_arg_slots_distinct r && vget_keys_distinct tsm r (fst store_kv)
    then // Check that the keys match
         if r.vget_key = fst store_kv
         then //Second check that the values match
              if Some r.vget_value = snd store_kv
              then begin
                let b = true in
                rewrite (VT.thread_state_inv_core t (vget_impl_tsm tsm r store_kv))
                        (if b
                         then VT.thread_state_inv_core t (vget_impl_tsm tsm r store_kv)
                         else VT.thread_state_inv_core t tsm);
                return b           
              end
              else begin
                let b = false in
                rewrite (VT.thread_state_inv_core t tsm)
                        (if b
                         then VT.thread_state_inv_core t (vget_impl_tsm tsm r store_kv)
                         else VT.thread_state_inv_core t tsm);
                return b
              end
         else begin
           let b = false in
           rewrite (VT.thread_state_inv_core t tsm)
                   (if b
                    then VT.thread_state_inv_core t (vget_impl_tsm tsm r store_kv)
                    else VT.thread_state_inv_core t tsm);
           return b
         end
    else begin
      let b = false in
      rewrite (VT.thread_state_inv_core t tsm)
              (if b
               then VT.thread_state_inv_core t (vget_impl_tsm tsm r store_kv)
               else VT.thread_state_inv_core t tsm);
      return b
    end

//
// The main vget function
//
// Its signature is same as Zeta.Steel.Application::run_app_function,
//   with a precondition that pl.fid == vget
//
let run_vget 
  (#log_perm:perm)
  (#log_bytes:Ghost.erased bytes)
  (log_len: U32.t)
  (pl: runApp_payload)
  (pl_pos:U32.t)
  (log_array:larray U8.t log_len {
    U32.v pl_pos + U32.v pl.rest.len <= Seq.length log_bytes /\
    U32.v log_len == Seq.length log_bytes /\
    Ghost.reveal pl.rest.ebytes == Seq.slice log_bytes (U32.v pl_pos) (U32.v pl_pos + U32.v pl.rest.len) })
  (#out_bytes: Ghost.erased bytes)
  (out_len:U32.t)
  (out_offset:U32.t{U32.v out_offset <= Seq.length out_bytes})
  (out:larray U8.t out_len)
  (#tsm:M.thread_state_model)
  (t:V.thread_state_t)
  : ST verify_runapp_result
       (V.thread_state_inv t tsm
          `star`
        A.pts_to log_array log_perm log_bytes
          `star`
        A.pts_to out full_perm out_bytes)
       (fun res ->
        A.pts_to log_array log_perm log_bytes
          `star`
        verify_runapp_entry_post tsm t pl out_bytes out_offset out res)
       (requires not tsm.failed /\ pl.fid == S.vget_id)
       (ensures fun _ -> True)
  = // Parse the input log
    let ropt = F.kvstore_vget_args_parser log_len pl_pos pl.rest.len log_array in
    match ropt with
    | None -> return Run_app_parsing_failure
    | Some (r, consumed) ->
      // Check that we consumed all the bytes
      if consumed = pl.rest.len
      then begin
        // For all slots check that they are in range
        if U16.lt r.vget_slot AT.store_size
        then begin
          // Get to thread_state_inv_core
          VT.elim_thread_state_inv t;
          // Read store for all the slots
          let kvopt = VT.read_store_app t r.vget_slot in
          match kvopt with
          | None ->
            VT.intro_thread_state_inv t;
            return Run_app_verify_failure
          | Some (k, vopt) ->
            // After we have read all the slots, call impl, with the input and store values
            let b = vget_impl t r (k, vopt) in
            if b
            then begin
              // We now have to match up to TSM.runapp
              // First eliminate conditional
              rewrite (if b
                       then VT.thread_state_inv_core t (vget_impl_tsm tsm r (k, vopt))
                       else VT.thread_state_inv_core t tsm)
                      (VT.thread_state_inv_core t (vget_impl_tsm tsm r (k, vopt)));
              // This write_slots is what is used in TSM.runapp,
              //   so assert equality and rewrite to write_slots
              let tsm_write_slots =
                TSM.write_slots tsm (vget_spec_slots r)
                                    (vget_spec_out_vals tsm r) in
              assert (Seq.equal (vget_impl_tsm tsm r (k, vopt)).store tsm_write_slots.store);
              rewrite (VT.thread_state_inv_core t (vget_impl_tsm tsm r (k, vopt)))
                      (VT.thread_state_inv_core t tsm_write_slots);

              // Final tsm as computed by TSM.runapp
              let tsm_final =
                {tsm_write_slots
                 with app_results = Seq.snoc tsm_write_slots.app_results (vget_app_result tsm r);
                      processed_entries=Seq.snoc tsm.processed_entries (RunApp pl)} in

              assert (TSM.verify_step_model tsm (RunApp pl) == tsm_final);
              assert (VT.tsm_entries_invariant tsm_final);

              // Call helper in VT to get the invariant
              VT.restore_thread_state_inv_app t
                (Seq.snoc tsm_write_slots.app_results (vget_app_result tsm r))
                (Seq.snoc tsm.processed_entries (RunApp pl));

              // Not writing any output
              let wrote = 0ul in

              intro_pure (n_out_bytes
                            tsm
                            (TSM.verify_step_model tsm (RunApp pl))
                            out_offset
                            wrote
                            out_bytes
                            out_bytes);
              return (Run_app_success wrote)
            end
            else begin
              rewrite (if b
                       then VT.thread_state_inv_core t (vget_impl_tsm tsm r (k, vopt))
                       else VT.thread_state_inv_core t tsm)
                      (VT.thread_state_inv_core t tsm);
              VT.intro_thread_state_inv t;
              return Run_app_verify_failure
            end
        end
        else return Run_app_verify_failure
      end
      else return Run_app_parsing_failure

/// Same exercise for vput

let vput_spec_args (r:F.vput_args_t)
  : GTot (App.interp_code S.adm S.vput_spec_arg_t)
  = r.vput_key, r.vput_value

let vput_spec_slots (r:F.vput_args_t)
  : GTot (Seq.seq slot_id)
  = Seq.create 1 r.vput_slot

let vput_spec_out_vals (tsm:TSM.thread_state_model) (r:F.vput_args_t)
  : Ghost (r:Seq.seq (App.app_value_nullable S.adm){Seq.length r == S.vput_spec_arity})
          (requires Some? (TSM.read_slots tsm (vput_spec_slots r)))
          (ensures fun _ -> True)
  = let recs = Some?.v (TSM.read_slots tsm (vput_spec_slots r)) in
    let _, _, out_vals = S.vput_spec_f (vput_spec_args r) recs in
    out_vals

let vput_app_result (tsm:TSM.thread_state_model) (r:F.vput_args_t)
  : Ghost app_result_entry
      (requires Some? (TSM.read_slots tsm (vput_spec_slots r)))
      (ensures fun _ -> True)
  = let recs = Some?.v (TSM.read_slots tsm (vput_spec_slots r)) in
    let _, res, _ = S.vput_spec_f (vput_spec_args r) recs in  
    (| S.vput_id, vput_spec_args r, recs, res |)

let vput_app_success (tsm:TSM.thread_state_model) (r:F.vput_args_t)
  : Ghost bool
      (requires Some? (TSM.read_slots tsm (vput_spec_slots r)))
      (ensures fun _ -> True)
  = let recs = Some?.v (TSM.read_slots tsm (vput_spec_slots r)) in
    let r, _, _ = S.vput_spec_f (vput_spec_args r) recs in
    App.Fn_success? r

inline_for_extraction
let vput_arg_slots_distinct (r:F.vput_args_t)
  : Pure bool
      (requires True)
      (ensures fun b -> b <==> Zeta.SeqAux.distinct_elems_comp (vput_spec_slots r))
  = true

inline_for_extraction
let vput_keys_distinct (tsm:TSM.thread_state_model) (r:F.vput_args_t) (k:AT.key_type)
  : Pure bool
      (requires Some? (TSM.read_slots tsm (vput_spec_slots r)) /\
                (let kvs = Some?.v (TSM.read_slots tsm (vput_spec_slots r)) in
                 Seq.equal (Zeta.SeqAux.map fst kvs) (Seq.create 1 k)))
      (ensures fun b -> b <==> TSM.check_distinct_keys (Some?.v (TSM.read_slots tsm (vput_spec_slots r))))
  = true

//
// Note that it updates the store
//   (matches with what VT.write_store gives us)
//
let vput_impl_tsm
  (tsm:TSM.thread_state_model)
  (r:F.vput_args_t)
  (store_kv:(F.key_t & option F.value_t){slot_value_is_kv tsm r.vput_slot store_kv})
  : TSM.thread_state_model
  = VT.update_tsm_slot_value tsm r.vput_slot (DValue (Some r.vput_value))

//
// This writes the store also
//
let vput_impl (#tsm:TSM.thread_state_model)
  (t:VT.thread_state_t)
  (r:F.vput_args_t)
  (store_kv:(F.key_t & option F.value_t){slot_value_is_kv tsm r.vput_slot store_kv})
  : ST bool
      (VT.thread_state_inv_core t tsm)
      (fun b -> 
       if b
       then VT.thread_state_inv_core t (vput_impl_tsm tsm r store_kv)
       else VT.thread_state_inv_core t tsm)
      (requires True)
      (ensures fun b ->
         (b ==> (r.vput_key == fst store_kv /\
                Some r.vput_value == snd store_kv /\
                Zeta.SeqAux.distinct_elems_comp (vput_spec_slots r) /\
                TSM.check_distinct_keys (Some?.v (TSM.read_slots tsm (vput_spec_slots r))) /\
                vput_app_success tsm r)))
  = //Check distinctness of keys and slots
    if vput_arg_slots_distinct r && vput_keys_distinct tsm r (fst store_kv)
    then // Check that the keys match
         if r.vput_key = fst store_kv
         then //Second check that the values match
              if Some r.vput_value = snd store_kv
              then begin
                VT.write_store t r.vput_slot (DValue (Some r.vput_value));
                let b = true in
                rewrite (VT.thread_state_inv_core t (vput_impl_tsm tsm r store_kv))
                        (if b
                         then VT.thread_state_inv_core t (vput_impl_tsm tsm r store_kv)
                         else VT.thread_state_inv_core t tsm);
                return b           
              end
              else begin
                let b = false in
                rewrite (VT.thread_state_inv_core t tsm)
                        (if b
                         then VT.thread_state_inv_core t (vput_impl_tsm tsm r store_kv)
                         else VT.thread_state_inv_core t tsm);
                return b
              end
         else begin
           let b = false in
           rewrite (VT.thread_state_inv_core t tsm)
                   (if b
                    then VT.thread_state_inv_core t (vput_impl_tsm tsm r store_kv)
                    else VT.thread_state_inv_core t tsm);
           return b
         end
    else begin
      let b = false in
      rewrite (VT.thread_state_inv_core t tsm)
              (if b
               then VT.thread_state_inv_core t (vput_impl_tsm tsm r store_kv)
               else VT.thread_state_inv_core t tsm);
      return b
    end

let run_vput 
  (#log_perm:perm)
  (#log_bytes:Ghost.erased bytes)
  (log_len: U32.t)
  (pl: runApp_payload)
  (pl_pos:U32.t)
  (log_array:larray U8.t log_len {
    U32.v pl_pos + U32.v pl.rest.len <= Seq.length log_bytes /\
    U32.v log_len == Seq.length log_bytes /\
    Ghost.reveal pl.rest.ebytes == Seq.slice log_bytes (U32.v pl_pos) (U32.v pl_pos + U32.v pl.rest.len) })
  (#out_bytes: Ghost.erased bytes)
  (out_len:U32.t)
  (out_offset:U32.t{U32.v out_offset <= Seq.length out_bytes})
  (out:larray U8.t out_len)
  (#tsm:M.thread_state_model)
  (t:V.thread_state_t)
  : ST verify_runapp_result
       (V.thread_state_inv t tsm
          `star`
        A.pts_to log_array log_perm log_bytes
          `star`
        A.pts_to out full_perm out_bytes)
       (fun res ->
        A.pts_to log_array log_perm log_bytes
          `star`
        verify_runapp_entry_post tsm t pl out_bytes out_offset out res)
       (requires not tsm.failed /\ pl.fid == S.vput_id)
       (ensures fun _ -> True)
  = let ropt = F.kvstore_vput_args_parser log_len pl_pos pl.rest.len log_array in
    match ropt with
    | None -> return Run_app_parsing_failure
    | Some (r, consumed) ->
      if consumed = pl.rest.len
      then begin
        if U16.lt r.vput_slot AT.store_size
        then begin
          VT.elim_thread_state_inv t;
          let kvopt = VT.read_store_app t r.vput_slot in
          match kvopt with
          | None ->
            VT.intro_thread_state_inv t;
            return Run_app_verify_failure
          | Some (k, vopt) ->
            let b = vput_impl t r (k, vopt) in
            if b
            then begin
              rewrite (if b
                       then VT.thread_state_inv_core t (vput_impl_tsm tsm r (k, vopt))
                       else VT.thread_state_inv_core t tsm)
                      (VT.thread_state_inv_core t (vput_impl_tsm tsm r (k, vopt)));
              let tsm_write_slots =
                TSM.write_slots tsm (vput_spec_slots r)
                                    (vput_spec_out_vals tsm r) in
              assert (Seq.equal (vput_impl_tsm tsm r (k, vopt)).store tsm_write_slots.store);
              rewrite (VT.thread_state_inv_core t (vput_impl_tsm tsm r (k, vopt)))
                      (VT.thread_state_inv_core t tsm_write_slots);

              let tsm_final =
                {tsm_write_slots
                 with app_results = Seq.snoc tsm_write_slots.app_results (vput_app_result tsm r);
                      processed_entries=Seq.snoc tsm.processed_entries (RunApp pl)} in

              assert (TSM.verify_step_model tsm (RunApp pl) == tsm_final);
              assert (VT.tsm_entries_invariant tsm_final);

              VT.restore_thread_state_inv_app t
                (Seq.snoc tsm_write_slots.app_results (vput_app_result tsm r))
                (Seq.snoc tsm.processed_entries (RunApp pl));

              let wrote = 0ul in

              intro_pure (n_out_bytes
                            tsm
                            (TSM.verify_step_model tsm (RunApp pl))
                            out_offset
                            wrote
                            out_bytes
                            out_bytes);
              return (Run_app_success wrote)
            end
            else begin
              rewrite (if b
                       then VT.thread_state_inv_core t (vput_impl_tsm tsm r (k, vopt))
                       else VT.thread_state_inv_core t tsm)
                      (VT.thread_state_inv_core t tsm);
              VT.intro_thread_state_inv t;
              return Run_app_verify_failure
            end
        end
        else return Run_app_verify_failure
      end
      else return Run_app_parsing_failure

let run_app_function #log_perm #log_bytes log_len pl pl_pos log_array
  #out_bytes out_len out_offset out
  #tsm t
  = if pl.fid = S.vget_id
    then run_vget log_len pl pl_pos log_array out_len out_offset out t
    else if pl.fid = S.vput_id
    then run_vput log_len pl pl_pos log_array out_len out_offset out t
    else return Run_app_parsing_failure

friend Zeta.Steel.KeyUtils
friend Zeta.KeyValueStore.Spec

let key_type_to_base_key k =
  let bk = {
    k = ({
      v3 = k;
      v2 = 0uL;
      v1 = 0uL;
      v0 = 0uL;
    });

   significant_digits = 256us;
  } in

  lower_lift_id bk;
  return bk
