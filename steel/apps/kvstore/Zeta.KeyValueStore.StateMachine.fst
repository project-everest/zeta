module Zeta.KeyValueStore.StateMachine

module SeqAux = Zeta.SeqAux
module I = Zeta.Interleave

module F = Zeta.KeyValueStore.Formats


type log_entry =
  | Vget: k:F.key_t -> v:F.value_t -> log_entry
  | Vput: k:F.key_t -> v:F.value_t -> log_entry

type state = Map.t F.key_t (option F.value_t)

let get (st:state) (k:F.key_t) : option F.value_t =
  Map.sel st k

let put (st:state) (k:F.key_t) (v:F.value_t) : state =
  Map.upd st k (Some v)

let initial_state : state = Map.const_on Set.empty None

let simulate_step (entry:log_entry) (st:state) : option state =
  match entry with
  | Vget k v ->
    let st_v = get st k in
    if st_v = None then None
    else let Some v' = st_v in
         if v' = v then Some st else None
  | Vput k v -> Some (put st k v)

let rec simulate (s:Seq.seq log_entry)
  : Tot (option state)
        (decreases Seq.length s)
  = if Seq.length s = 0
    then Some initial_state
    else let s_pfx = SeqAux.prefix s (Seq.length s - 1) in
         match simulate s_pfx with
         | None -> None
         | Some st -> simulate_step (Seq.last s) st

type log = Seq.seq log_entry

let valid_log (s:log) = Some? (simulate s)

type llog = Seq.seq log

let seq_consistent (ss:llog) = exists s. I.interleave s ss /\ valid_log s

module AppSim = Zeta.AppSimulate
module S = Zeta.KeyValueStore.Spec

let map_entry (e:AppSim.appfn_call_res S.kv_params) : log_entry =
  if e.fid_cr = S.vget_id
  then let t : F.key_t & F.value_t = e.arg_cr in
       Vget (fst t) (snd t)
  else let t : F.key_t & F.value_t = e.arg_cr in
       Vput (fst t) (snd t)

let map_log (s:Seq.seq (AppSim.appfn_call_res S.kv_params)) : log =
  SeqAux.map map_entry s

let map_llog (ss:Seq.seq (Seq.seq (AppSim.appfn_call_res S.kv_params))) : llog =
  SeqAux.map map_log ss

let map_seq_consistency (ss:Seq.seq (Seq.seq (AppSim.appfn_call_res S.kv_params)))
  : Lemma (requires AppSim.seq_consistent ss)
          (ensures (seq_consistent (map_llog ss)))
  = eliminate exists is. I.interleave #(AppSim.appfn_call_res S.kv_params) is ss /\ AppSim.valid_call_result is
    returns seq_consistent (map_llog ss)
    with _. begin
      admit ()
    end
