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

#set-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"

assume val admit__ (#a:Type) (#p:vprop) (#q:post_t a) (_:unit)
  : STF a p q (True) (fun _ -> False)

let slot_value_is_kv
  (tsm:TSM.thread_state_model)
  (slot:slot_id)
  (store_kv:AT.key_type & option AT.value_type)
  = U16.v slot < U16.v AT.store_size /\
    Some? (Seq.index tsm.store (U16.v slot)) /\
    (let Some se = Seq.index tsm.store (U16.v slot) in
     se.key == ApplicationKey (fst store_kv) /\
     se.value == DValue (snd store_kv))
    
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

let vget_impl (#tsm:TSM.thread_state_model)
  (t:VT.thread_state_t)
  (r:F.vget_args_t)
  (store_kv:(F.key_t & option F.value_t){slot_value_is_kv tsm r.vget_slot store_kv})
  : ST bool
      (VT.thread_state_inv_core t tsm)
      (fun b -> 
       if b
       then VT.thread_state_inv_core t tsm
       else VT.thread_state_inv_core t tsm)
      (requires True)
      (ensures fun b ->
         (b ==> (r.vget_key == fst store_kv /\
                Some r.vget_value == snd store_kv /\
                vget_app_success tsm r)))
  = if r.vget_key = fst store_kv
    then if Some r.vget_value = snd store_kv
         then begin
           let b = true in
           rewrite (VT.thread_state_inv_core t tsm)
                   (if b
                    then VT.thread_state_inv_core t tsm
                    else VT.thread_state_inv_core t tsm);
           return b           
         end
         else begin
           let b = false in
           rewrite (VT.thread_state_inv_core t tsm)
                   (if b
                    then VT.thread_state_inv_core t tsm
                    else VT.thread_state_inv_core t tsm);
           return b
         end
    else begin
      let b = false in
      rewrite (VT.thread_state_inv_core t tsm)
              (if b
               then VT.thread_state_inv_core t tsm
               else VT.thread_state_inv_core t tsm);
      return b
    end

#push-options "--z3rlimit 50"
let run_vget 
  (#log_perm:perm)
  (#log_bytes:Ghost.erased bytes)
  (log_len: Ghost.erased U32.t)
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
  = let ropt = F.vget_args_parser log_len pl_pos pl.rest.len log_array in
    match ropt with
    | None -> return Run_app_parsing_failure
    | Some (r, consumed) ->
      if consumed = pl.rest.len
      then begin
        if U16.v r.vget_slot < U16.v AT.store_size
        then begin
          VT.elim_thread_state_inv t;
          let kvopt = VT.read_store_app t r.vget_slot in
          match kvopt with
          | None ->
            VT.intro_thread_state_inv t;
            return Run_app_verify_failure
          | Some (k, vopt) ->
            let b = vget_impl t r (k, vopt) in
            if b
            then begin
              let tsm_impl = tsm in
              rewrite (if b
                       then VT.thread_state_inv_core t tsm
                       else VT.thread_state_inv_core t tsm)
                      (if b
                       then VT.thread_state_inv_core t tsm_impl
                       else VT.thread_state_inv_core t tsm);
              rewrite (if b
                       then VT.thread_state_inv_core t tsm_impl
                       else VT.thread_state_inv_core t tsm)
                      (VT.thread_state_inv_core t tsm_impl);
              let tsm_write_slots =
                TSM.write_slots tsm (vget_spec_slots r)
                                    (vget_spec_out_vals tsm r) in
              assert (Seq.equal tsm_impl.store tsm_write_slots.store);
              rewrite (VT.thread_state_inv_core t tsm_impl)
                      (VT.thread_state_inv_core t tsm_write_slots);

              assume (Zeta.SeqAux.distinct_elems_comp (vget_spec_slots r));
              assume (TSM.check_distinct_keys (Some?.v (TSM.read_slots tsm (vget_spec_slots r))));

              let tsm_final =
                {tsm_write_slots
                 with app_results = Seq.snoc tsm_write_slots.app_results (vget_app_result tsm r);
                      processed_entries=Seq.snoc tsm.processed_entries (RunApp pl)} in

              assert (TSM.verify_step_model tsm (RunApp pl) == tsm_final);
              assert (VT.tsm_entries_invariant tsm_final);

              VT.restore_thread_state_inv_app t
                (Seq.snoc tsm_write_slots.app_results (vget_app_result tsm r))
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
                       then VT.thread_state_inv_core t tsm
                       else VT.thread_state_inv_core t tsm)
                      (VT.thread_state_inv_core t tsm);
              VT.intro_thread_state_inv t;
              return Run_app_verify_failure
            end
        end
        else return Run_app_verify_failure
      end
      else return Run_app_parsing_failure
#pop-options

let run_app_function #log_perm #log_bytes log_len pl pl_pos log_array
  #out_bytes out_len out_offset out
  #tsm t
  = if pl.fid = S.vget_id
    then run_vget log_len pl pl_pos log_array out_len out_offset out t
    else admit__ ()

    
    // if pl.fid = KVS.vput_id
    // then begin
    //   assume (not tsm.failed);
    //   let ropt = KVF.vput_args_parser log_len pl_pos pl.rest.len log_array in
    //   match ropt with
    //   | None -> return Run_app_parsing_failure
    //   | Some (r, consumed) ->
    //     //
    //     // TODO: need to change the type in Zeta.Steel.Formats.fsti,
    //     //       that file is generated by EverParse
    //     //
    //     assume (U16.v r.vput_slot < U16.v KAT.store_size);
    //     let kvopt = VT.read_store t r.vput_slot in
    //     match kvopt with
    //     | None -> return Run_app_verify_failure
    //     | Some kv ->
    //       match kv.key, kv.value with
    //       | InternalKey _, _ -> return Run_app_verify_failure
    //       | _, MValue _ -> return Run_app_verify_failure
    //       | ApplicationKey k, DValue v_store ->
    //         if r.vput_key = k
    //         then begin
    //           VT.elim_thread_state_inv t;
    //           VT.write_store #tsm t r.vput_slot (DValue (Some r.vput_value));
    //           assert (ApplicationKey? (TSM.key_of_slot tsm r.vput_slot));
    //           assert (TSM.has_slot tsm r.vput_slot);
    //           assert (Map.contains aprm.tbl pl.fid);
    //           assert (spec_app_parser pl.fid pl.rest.ebytes ==
    //                   Some (((r.vput_key, r.vput_value), Seq.create 1 r.vput_slot), U32.v consumed));
    //           assume (consumed == pl.rest.len);
    //           assert (Zeta.SeqAux.distinct_elems_comp (Seq.create 1 r.vput_slot));
    //           assert (
    //             let slots = Seq.create 1 r.vput_slot in
    //             let arg = r.vput_key, r.vput_value in
    //             let recs = Some?.v (TSM.read_slots tsm (Seq.create 1 r.vput_slot)) in
    //             let out_vals = Seq.create 1 (App.DValue r.vput_value) in
    //             let tsm' = {tsm with app_results=Seq.Properties.snoc tsm.app_results (| pl.fid, arg, recs, () |)} in
    //             let tsm' = TSM.write_slots tsm' slots out_vals in
    //             let tsm' = {tsm' with processed_entries = Seq.snoc tsm.processed_entries (RunApp pl)} in
    //             tsm' == TSM.verify_step_model tsm (RunApp pl) /\
    //             tsm' == {(VT.update_tsm_slot_value tsm r.vput_slot (DValue (Some r.vput_value))) with
    //                      TSM.app_results=Seq.Properties.snoc tsm.app_results (| pl.fid, arg, recs, () |);
    //                      TSM.processed_entries = Seq.snoc tsm.processed_entries (RunApp pl)});
    //           let tsm' = {(VT.update_tsm_slot_value tsm r.vput_slot (DValue (Some r.vput_value))) with
    //                      TSM.app_results=Seq.Properties.snoc tsm.app_results (| pl.fid, (r.vput_key, r.vput_value), (Some?.v (TSM.read_slots tsm (Seq.create 1 r.vput_slot))), () |);
    //                      TSM.processed_entries = Seq.snoc tsm.processed_entries (RunApp pl)} in
    //           restore_thread_state_inv_core_put t
    //             (VT.update_tsm_slot_value tsm r.vput_slot (DValue (Some r.vput_value)))
    //             (Seq.Properties.snoc tsm.app_results (| pl.fid, (r.vput_key, r.vput_value), (Some?.v (TSM.read_slots tsm (Seq.create 1 r.vput_slot))), () |))
    //             (Seq.snoc tsm.processed_entries (RunApp pl));
    //           assert (VT.tsm_entries_invariant tsm');
    //           VT.intro_thread_state_inv #_ #tsm' t;
    //           let wrote = 0ul in
    //           assume (n_out_bytes
    //                     tsm
    //                     (TSM.verify_step_model tsm (RunApp pl))
    //                     out_offset
    //                     wrote
    //                     out_bytes
    //                     out_bytes);
    //           intro_pure (n_out_bytes
    //                         tsm
    //                         (TSM.verify_step_model tsm (RunApp pl))
    //                         out_offset
    //                         wrote
    //                         out_bytes
    //                         out_bytes);
    //           return (Run_app_success wrote)
    //         end
    //         else return Run_app_verify_failure
    // end
    // else return Run_app_verify_failure

let key_type_to_base_key _ = admit__ ()
