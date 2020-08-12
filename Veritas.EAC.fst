module Veritas.EAC

open FStar.Seq
open Veritas.Hash
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.SeqAux
open Veritas.SeqMachine
open Veritas.State
open Veritas.StateSeqMachine
open Veritas.Verifier

//Allow the solver to unroll recursive functions at most once (fuel)
#push-options "--max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"

let is_evict (e: vlog_entry): bool =
  match e with
  | EvictM _ _ -> true
  | EvictB _ _ -> true
  | EvictBM _ _ _ -> true
  | _ -> false

type evict_vlog_entry = e:vlog_entry {is_evict e}
type nevict_vlog_entry = e:vlog_entry {not (is_evict e)}

type vlog_entry_ext =
  | NEvict: e:nevict_vlog_entry -> vlog_entry_ext
  | Evict: e:evict_vlog_entry -> v:value -> vlog_entry_ext

type vlog_ext = seq (vlog_entry_ext)

type eac_state =
  | EACFail: eac_state
  | EACInit: eac_state
  | EACInCache: m:add_method -> v:value -> eac_state
  | EACEvicted: m:add_method -> v:value -> eac_state

let eac_add (e: vlog_entry_ext) (s: eac_state) : eac_state =
  match s with
  | EACFail -> EACFail
  | EACInit -> (
    match e with
    | NEvict (AddM (k,v) _) -> if v = init_value k then EACInCache MAdd v
                               else EACFail
    | _ -> EACFail
    )

  | EACInCache m v -> (
    match e with
    | NEvict (Get _ v') -> if (DVal v') = v then s
                           else EACFail
    | NEvict (Put _ v') -> if (DVal? v) then EACInCache m (DVal v')
                           else EACFail
    | Evict (EvictM _ _) v' -> if DVal? v && v' <> v then EACFail
                               else EACEvicted MAdd v
    | Evict (EvictBM _ _ _) v' -> if DVal? v && v' <> v || m <> MAdd then EACFail
                                  else EACEvicted BAdd v
    | Evict (EvictB _ _) v' ->  if DVal? v && v' <> v || m <> BAdd then EACFail
                                else EACEvicted BAdd v
    | _ -> EACFail
    )

  | EACEvicted m v -> (
    match e with
    | NEvict (AddM (_,v') _) -> if v' = v && m = MAdd then EACInCache MAdd v
                                else EACFail
    | NEvict (AddB (_,v') _ _) -> if v' = v && m = BAdd then EACInCache BAdd v
                                else EACFail
    | _ -> EACFail
  )

let eac_smk = SeqMachine EACInit EACFail eac_add

let to_vlog_entry (ee:vlog_entry_ext): vlog_entry =
  match ee with
  | Evict e _ -> e
  | NEvict e -> e

let vlog_entry_key (e: vlog_entry_ext): key =
  match (to_vlog_entry e) with
  | Get k _ -> k
  | Put k _ -> k
  | AddM (k,_) _ -> k
  | EvictM k _ -> k
  | AddB (k,_) _ _ -> k
  | EvictB k _ -> k
  | EvictBM k _ _ -> k

let eac_sm = PSM eac_smk vlog_entry_key

(* evict add consistency *)
let eac (l:vlog_ext) = valid_all eac_sm l

(* refinement of evict add consistent logs *)
type eac_log = l:vlog_ext{eac l}

(* the state operations of a vlog *)
let is_state_op (e: vlog_entry): bool =
  match e with
  | Get k v -> true
  | Put k v -> true
  | _ -> false

(* map vlog entry to state op *)
let to_state_op (e:vlog_entry {is_state_op e}): state_op =
  match e with
  | Get k v -> Veritas.State.Get k v
  | Put k v -> Veritas.State.Put k v

(* filter out the state ops of vlog *)
let to_state_op_vlog (l: vlog) =
  map to_state_op (filter_refine is_state_op l)

(* valid eac states *)
let valid_eac_state (st:eac_state): bool = not (EACFail? st)

(* value of a valid state *)
let value_of (st:eac_state {valid_eac_state st}): value =
  match st with
  | EACInit -> DVal Null
  | EACInCache _ v -> v
  | EACEvicted _ v -> v

let to_vlog (l:vlog_ext) =
  map to_vlog_entry l

let lemma_comm (le:vlog_ext) (k:data_key):
  Lemma (to_state_op_vlog (to_vlog (partn eac_sm k le)) =
         partn ssm k (to_state_op_vlog (to_vlog le))) =
  let lek = partn eac_sm k le in
  let lk = to_vlog lek in
  let lks = to_state_op_vlog lk in
  let l = to_vlog le in
  let ls = to_state_op_vlog l in
  let lsk = partn ssm k ls in
  admit()

let has_some_put (l:vlog) =
  exists_sat_elems Put? l

let last_put_idx (l:vlog{has_some_put l}) =
  last_index Put? l

let last_put_value_or_null (l:vlog) =
  if has_some_put l then Put?.v (index l (last_put_idx l))
  else Null

//let lemma_eac_add_closure (st: eac_state {EACFail st ||

let lemma_value_type (le:vlog_ext {length le > 0}):
  Lemma (EACFail = seq_machine_run eac_smk le \/
         EACFail <> seq_machine_run eac_smk (prefix le 1) /\
         DVal? (value_of (seq_machine_run eac_smk le)) =
         DVal? (value_of (seq_machine_run eac_smk (prefix le 1)))) =

  admit()

let lemma_first_entry_is_madd (le:vlog_ext):
  Lemma (requires (valid eac_smk le /\ length le > 0))
        (ensures (AddM? (to_vlog_entry (index le 0)))) =
  let le1 = prefix le 1 in
  let st1 = seq_machine_run eac_smk le1 in
  lemma_valid_prefix eac_smk le 1;
  lemma_reduce_singleton EACInit eac_add le1;
  assert(st1 = eac_add (index le 0) EACInit);
  ()

let rec lemma_data_val_state_implies_last_put (le:vlog_ext):
  Lemma (requires (valid eac_smk le /\
                   DVal? (value_of (seq_machine_run eac_smk le))))
        (ensures (DVal?.v (value_of (seq_machine_run eac_smk le)) =
                  last_put_value_or_null (to_vlog le)))
        (decreases (length le)) =
  let l = to_vlog le in
  let n = length le in
  let st = seq_machine_run eac_smk le in

  if n = 0 then (
    lemma_reduce_empty EACInit eac_add;
    lemma_empty le;
    assert (EACInit = seq_machine_run eac_smk le);
    ()
  )

  else if n = 1 then (
    lemma_first_entry_is_madd le;
    lemma_reduce_singleton EACInit eac_add le;

    if has_some_put l then (
      let i = last_put_idx l in
      ()
    )
    else match (index le 0) with
    | NEvict (AddM (k, v) _ ) ->
      assert(value_of st = v);
      ()
  )

  else (
    let le' = prefix le (n - 1) in
    let l' = prefix l (n - 1) in
    lemma_map_prefix to_vlog_entry le (n - 1);
    lemma_valid_prefix eac_smk le (n - 1);

    // le and le' have the same value type
    lemma_value_type le;
    lemma_value_type le';
    assert(DVal? (value_of (seq_machine_run eac_smk le')));

    // induction
    lemma_data_val_state_implies_last_put le';

    // IH
    let st' = seq_machine_run eac_smk le' in
    assert(DVal?.v (value_of st') = last_put_value_or_null (to_vlog le'));

    lemma_reduce_append2 EACInit eac_add le;
    assert(st = eac_add (index le (n - 1)) st');

    if Put? (to_vlog_entry (index le (n - 1))) then
      lemma_last_index_last_elem_sat Put? l

    else (
      assert(value_of st' = value_of st);
      lemma_last_index_last_elem_nsat Put? l;

      if has_some_put l' then
        lemma_last_index_prefix Put? l (n - 1)
      else ()

    )
  )

let lemma_get_implies_data_val_state (le:vlog_ext) (i:seq_index le):
  Lemma (requires (valid eac_smk le /\ Get? (to_vlog_entry (index le i))))
        (ensures (valid eac_smk (prefix le i) /\
                  EACInCache? (seq_machine_run eac_smk (prefix le i)) /\
                  DVal? (value_of (seq_machine_run eac_smk (prefix le i))))) =
  let lei = prefix le i in
  let lei' = prefix le (i + 1) in

  lemma_valid_prefix eac_smk le i;
  lemma_valid_prefix eac_smk le (i + 1);
  lemma_reduce_append2 EACInit eac_add lei';
  ()

let lemma_eac_k_implies_valid_get (le:vlog_ext) (i:seq_index le):
  Lemma (requires (valid eac_smk le /\ Get? (to_vlog_entry (index le i))))
        (ensures (Get?.v (to_vlog_entry (index le i)) =
                  last_put_value_or_null (to_vlog (prefix le i)))) =
  let n = length le in
  let lei = prefix le i in

  lemma_first_entry_is_madd le;
  assert(n > 1);

  lemma_get_implies_data_val_state le i;
  assert(valid eac_smk lei);
  assert(DVal? (value_of (seq_machine_run eac_smk lei)));

  lemma_data_val_state_implies_last_put lei;
  let sti = seq_machine_run eac_smk lei in
  assert(DVal? (value_of sti));

  let lei' = prefix le (i + 1) in
  lemma_valid_prefix eac_smk le (i + 1);
  assert(EACFail <> (seq_machine_run eac_smk lei'));

  lemma_reduce_append2 EACInit eac_add lei';
  assert(seq_machine_run eac_smk lei' = eac_add (index le i) sti);
  ()

let state_op_map (l:vlog) (i:seq_index (to_state_op_vlog l)):
  Tot (j:(seq_index l){is_state_op (index l j) /\
                       to_state_op (index l j) =  index (to_state_op_vlog l) i /\
                       to_state_op_vlog (prefix l j) = prefix (to_state_op_vlog l) i}) =
  let ls = to_state_op_vlog l in
  let j = filter_index_map is_state_op l i in
  lemma_filter_prefix_comm is_state_op l j;
  lemma_map_prefix to_state_op (filter_refine is_state_op l) i;
  assert(equal (prefix (filter_refine is_state_op l) i) (filter_refine is_state_op (prefix l j)));
  j

let lemma_last_put_map (l:vlog):
  Lemma (last_put_value_or_null l =
         last_put_value_or_null_k (to_state_op_vlog l)) =
  let ls = to_state_op_vlog l in
  if has_some_put l then (
    let j = last_put_idx l in
    let i = filter_index_inv_map is_state_op l j in
    assert(index ls i = to_state_op (index l j));
    lemma_last_index_correct2 Veritas.State.Put? ls i;
    let i' = last_put_idx_k ls in
    if i' = i then ()
    else (
      let j' = filter_index_map is_state_op l i' in
      lemma_filter_index_map_monotonic is_state_op l i i';
      lemma_filter_maps_correct is_state_op l j;
      lemma_last_index_correct2 Put? l j'
    )
  )
  else if has_some_put_k ls then
    let i = last_put_idx_k ls in
    let j = state_op_map l i in
    lemma_last_index_correct2 Put? l j
  else ()

let lemma_eac_k_implies_ssm_k_valid (le:eac_log) (k:data_key):
  Lemma (valid ssm_k (to_state_op_vlog (to_vlog (partn eac_sm k le)))) =
  let lek = partn eac_sm k le in
  let lk = to_vlog lek in
  let lks = to_state_op_vlog lk in
  if valid ssm_k lks then ()
  else (
    let i = max_valid_prefix ssm_k lks in
    let op = index lks i in

    lemma_first_invalid_implies_invalid_get (prefix lks (i + 1));
    assert(Veritas.State.Get?.v op <> last_put_value_or_null_k (prefix lks i));

    // index of entry in lk/lek that corresponds to i
    let j = (state_op_map lk i) in
    assert(to_state_op(index lk j) = op);
    lemma_eac_k_implies_valid_get lek j;
    lemma_map_prefix to_vlog_entry lek j;
    lemma_last_put_map (prefix lk j)
  )

(* evict add consistency implies rw-consistency *)
let lemma_eac_implies_rw_consistent (le:eac_log):
  Lemma (rw_consistent (to_state_op_vlog (to_vlog le))) =
  let l = to_vlog le in
  let s = to_state_op_vlog l in
  let rwc = valid_all_comp ssm s in
  lemma_state_sm_equiv_rw_consistent s;
  if rwc then () // nothing to prove if rw_consistent
  else (
    (* invalidating key *)
    let k = invalidating_key ssm s in
    lemma_eac_k_implies_ssm_k_valid le k;
    lemma_comm le k
  )
