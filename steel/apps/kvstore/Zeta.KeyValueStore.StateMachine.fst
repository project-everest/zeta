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

type app_log_entry = AppSim.appfn_call_res S.kv_params

let map_entry (e:app_log_entry) : log_entry =
  if e.fid_cr = S.vget_id
  then let t : F.key_t & F.value_t = e.arg_cr in
       Vget (fst t) (snd t)
  else let t : F.key_t & F.value_t = e.arg_cr in
       Vput (fst t) (snd t)

let map_log (s:Seq.seq app_log_entry) : log =
  SeqAux.map map_entry s

let map_llog (ss:Seq.seq (Seq.seq app_log_entry)) : llog =
  SeqAux.map map_log ss

let map_interleaving (#n:nat) (il:I.interleaving app_log_entry n)
  : I.interleaving log_entry n
  = let open Zeta.Interleave in
    SeqAux.map (fun i -> {
      e = map_entry i.e;
      s = i.s }) il

let interleaving_iseq_commutes
  (n:nat)
  (s:Seq.seq app_log_entry)
  (il:I.interleaving app_log_entry n)
  : Lemma (requires I.i_seq il == s)
          (ensures I.i_seq (map_interleaving il) == map_log s)
  = let open Zeta.Interleave in
    let aux (#a:_) (#n:_) (il:interleaving a n) (i:nat{i < Seq.length il})
      : Lemma (ensures Seq.index (i_seq il) i == (Seq.index il i).e)
              [SMTPat ()]
      = I.lemma_iseq_index il i in
    assert (Seq.equal (I.i_seq (map_interleaving il)) (map_log s))

let interleaving_sseq_commutes
  (n:nat)
  (ss:Seq.seq (Seq.seq app_log_entry))
  (il:I.interleaving app_log_entry n)
  : Lemma (requires I.s_seq il == ss)
          (ensures I.s_seq (map_interleaving il) == map_llog ss)
  = admit ()

let map_seq_consistency (ss:Seq.seq (Seq.seq (AppSim.appfn_call_res S.kv_params)))
  : Lemma (requires AppSim.seq_consistent ss)
          (ensures (seq_consistent (map_llog ss)))
  = eliminate exists is. I.interleave #(AppSim.appfn_call_res S.kv_params) is ss /\ AppSim.valid_call_result is
    returns seq_consistent (map_llog ss)
    with _. begin
      admit ()
    end
