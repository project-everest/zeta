module Zeta.KeyValueStore.StateMachine

module SeqAux = Zeta.SeqAux
module I = Zeta.Interleave

module F = Zeta.KeyValueStore.Formats

//
// State of a key value store is a map from keys to optional values
//

type state = Map.t F.key_t (option F.value_t)

let get (st:state) (k:F.key_t) : option F.value_t =
  Map.sel st k

let put (st:state) (k:F.key_t) (v:F.value_t) : state =
  Map.upd st k (Some v)

let initial_state : state = Map.const None

//
// Log entry is an operation on the state,
//   either a get, or a put
//

type log_entry =
  | Vget: k:F.key_t -> v:F.value_t -> log_entry
  | Vput: k:F.key_t -> v:F.value_t -> log_entry

type log = Seq.seq log_entry

//
// A single step of a state machine
//
// Returns None if the operation fails
//

let step (entry:log_entry) (st:state) : option state =
  match entry with
  | Vget k v ->
    let st_v = get st k in
    if st_v = None then None
    else let Some v' = st_v in
         if v' = v then Some st else None
  | Vput k v -> Some (put st k v)

//
// Sequence of steps
//

let rec steps (s:log)
  : Tot (option state)
        (decreases Seq.length s)
  = if Seq.length s = 0
    then Some initial_state
    else let s_pfx = SeqAux.prefix s (Seq.length s - 1) in
         match steps s_pfx with
         | None -> None
         | Some st -> step (Seq.last s) st


//
// A log is valid if stepping through it succeeds
//

let valid_log (s:log) = Some? (steps s)

//
// Logs for multiple threads
//

type llog = Seq.seq log


//
// Definition of sequential consistency
//

let seq_consistent (ss:llog) = exists s. I.interleave s ss /\ valid_log s

//
// We prove sequential consistency,
//   via a construction that's generic in the application functions
//
// The definition of sequential consistency for the generic construction
//   is AppSimulate.seq_consistent
//
// Below, we prove that the generic definition can be specialized to
//   the definition for key value store
//
// We sketch the statement of the lemma,
//   then the rest of the module proves it
//

module AppSim = Zeta.AppSimulate
module S = Zeta.KeyValueStore.Spec

type app_log_entry = AppSim.appfn_call_res S.kv_params

let map_entry (e:app_log_entry) : log_entry =
  if e.fid_cr = S.vget_id
  then let t : F.key_t & F.value_t = e.arg_cr in
       Vget (fst t) (snd t)
  else let t : F.key_t & F.value_t = e.arg_cr in
       Vput (fst t) (snd t)

let map_llog (ss:Seq.seq (Seq.seq app_log_entry)) : llog =
  SeqAux.map (fun s -> SeqAux.map map_entry s) ss

//
// Following is the statement of the map lemma that we prove below
//

val map_seq_consistency (ss:Seq.seq (Seq.seq app_log_entry))
  : Lemma (requires AppSim.seq_consistent ss)
          (ensures (seq_consistent (map_llog ss)))


//
// Rest of the module builds proof of map_seq_consistency
//

module App = Zeta.App
module SA = Zeta.SeqAux

//
// Correspondence between the kv state and generic app state
//

let state_maps_app_state (st:state) (app_st:AppSim.app_state S.kv_params.adm) =
  forall (k:F.key_t).
    match Map.sel st k, app_st k with
    | None, App.Null -> True
    | Some v_st, App.DValue v_app_st -> v_st == v_app_st
    | _, _ -> False

let initial_state_maps_initial_app_state ()
  : Lemma (state_maps_app_state initial_state (AppSim.init_app_state S.kv_params.adm))
  = ()

let map_fn_call (e:AppSim.appfn_call S.kv_params) : log_entry =
  if e.fid_c = S.vget_id
  then let t : F.key_t & F.value_t = e.arg_c in
       Vget (fst t) (snd t)
  else let t : F.key_t & F.value_t = e.arg_c in
       Vput (fst t) (snd t)

//
// Simulating one step
//

let map_simulate_step
  (fncall:AppSim.appfn_call S.kv_params)
  (app_st:AppSim.app_state S.kv_params.adm)
  (st:state)
  : Lemma
      (requires state_maps_app_state st app_st)
      (ensures (let ropt = AppSim.simulate_step fncall app_st in
                match ropt with
                | None -> True  // under-specified
                | Some (app_st, _res) ->
                  let sopt = step (map_fn_call fncall) st in
                  Some? sopt /\
                  state_maps_app_state (Some?.v sopt) app_st))
  = ()

let prefix_map_lemma (#a #b:_) (s:Seq.seq a) (i:nat{i <= Seq.length s}) (f:a -> b)
  : Lemma (SA.prefix (SA.map f s) i == SA.map f (SA.prefix s i))
          [SMTPat (SA.prefix (SA.map f s) i)]
  = assert (Seq.equal (SA.prefix (SA.map f s) i) (SA.map f (SA.prefix s i)))

//
// Simulating multiple steps
//

let rec map_simulate (fs:Seq.seq (AppSim.appfn_call S.kv_params))
  : Lemma
      (ensures (let ropt = AppSim.simulate fs in
                match ropt with
                | None -> True  // under-specified
                | Some (app_st, _sres) ->
                  let sopt = steps (SA.map map_fn_call fs) in
                  Some? sopt /\
                  state_maps_app_state (Some?.v sopt) app_st))
      (decreases Seq.length fs)
  = let n = Seq.length fs in
    if n = 0
    then ()
    else begin
      let fs_pfx = SA.prefix fs (n - 1) in
      let sopt = AppSim.simulate fs_pfx in
      map_simulate fs_pfx;
      match sopt with
      | None -> ()
      | Some (app_st, _) ->
        let Some st = steps (SA.map map_fn_call fs_pfx) in
        map_simulate_step (Seq.index fs (n - 1)) app_st st
    end

let map_valid_call_result (is:Seq.seq app_log_entry)
  : Lemma (requires AppSim.valid_call_result is)
          (ensures valid_log (SA.map map_entry is))
  = map_simulate (AppSim.app_fcs is);
    assert (Seq.equal (SA.map map_entry is) (SA.map map_fn_call (AppSim.app_fcs is)))

let map_log (s:Seq.seq app_log_entry) : log =
  SeqAux.map map_entry s

let map_seq_consistency (ss:Seq.seq (Seq.seq app_log_entry))
  : Lemma (requires AppSim.seq_consistent ss)
          (ensures (seq_consistent (map_llog ss)))
  = eliminate exists (is:Seq.seq app_log_entry). I.interleave is ss /\ AppSim.valid_call_result is
    returns seq_consistent (map_llog ss)
    with _. begin
      I.map_interleave is ss map_entry;
      assert (I.interleave (map_log is) (map_llog ss));
      map_valid_call_result is;
      introduce exists s. I.interleave s (map_llog ss) /\ valid_log s
      with (map_log is)
      and ()
    end
