module Veritas.Intermediate.Store

module R = Veritas.Record
module SA = Veritas.SeqAux
module V = Veritas.Verifier

let key = Veritas.Key.key
let value = Veritas.Record.value
let add_method = Veritas.Verifier.add_method

type slot_id = nat

type record = 
  | Record: k:key -> v:R.value_type_of k -> am:add_method -> record

type vstore = {
  data:Seq.seq (option record);
  is_map:bool;
}

let st_index (st:vstore) = SA.seq_index st.data

(* get record by slot_id *)
let get_record (st:vstore) (s:slot_id)
  : option record
  = if s >= Seq.length st.data then None else Seq.index st.data s

let contains_record (st:vstore) (s:slot_id)
  : bool
  = Some? (get_record st s)

let get_key_at (st:vstore) (s:slot_id{contains_record st s})
  : key
  = Record?.k (Some?.v (get_record st s))

let get_value_at (st:vstore) (s:slot_id{contains_record st s})
  : value
  = Record?.v (Some?.v (get_record st s))

let get_add_method_at (st:vstore) (s:slot_id{contains_record st s})
  : add_method
  = Record?.am (Some?.v (get_record st s))

(* get record by key *)
let lookup_key (st:vstore) (k:key) 
  : option record
  = let f ro = if None? ro then false
               else let Some r = ro in Record?.k r = k in
    let s = SA.filter f st.data in
    if Seq.length s = 0 then None
    else Seq.index s 0 

let contains_key (st:vstore) (k:key)
  : bool
  = Some? (lookup_key st k)

let lemma_lookup_key (st:vstore) (k:key) 
  : Lemma (requires (contains_key st k))
          (ensures (Record?.k (Some?.v (lookup_key st k)) = k))
  = let f ro = if None? ro then false
               else let Some r = ro in Record?.k r = k in
    SA.lemma_filter_correct1 f st.data 0

let lemma_contains_key (st:vstore) (s:slot_id{contains_record st s}) (k:key)
  : Lemma (requires (get_key_at st s = k))
          (ensures (contains_key st k))
  = let f ro = if None? ro then false
               else let Some r = ro in Record?.k r = k in
    let sq = SA.filter f st.data in
    SA.lemma_filter_exists f st.data;
    SA.lemma_filter_correct1 f st.data 0

let value_of (st:vstore) (k:key{contains_key st k})
  : R.value_type_of k
  = lemma_lookup_key st k;
    Record?.v (Some?.v (lookup_key st k))

let add_method_of (st:vstore) (k:key{contains_key st k})
  : add_method
  = Record?.am (Some?.v (lookup_key st k))

let update_record (st:vstore) (s:st_index st) (r:record)
  : vstore
  = { st with data = Seq.upd st.data s (Some r) }

let update_record_value 
  (st:vstore) 
  (s:st_index st{contains_record st s}) 
  (v:value{R.is_value_of (get_key_at st s) v})
  : vstore
  = let Some (Record k _ am) = get_record st s in
    update_record st s (Record k v am) 

let add_record (st:vstore) (s:st_index st) (k:key) (v:value{R.is_value_of k v}) (am:add_method)
  : vstore
  = update_record st s (Record k v am)

let evict_record (st:vstore) (s:st_index st)
  : vstore
  = { st with data = Seq.upd st.data s None }

let update_is_map (st:vstore) (b:bool) 
  : vstore 
  = { st with is_map = b }

(* slot_id s is consistent with key k *)
let slot_key_equiv (st:vstore) (s:slot_id) (k:key) : bool =
  not st.is_map || // trivially true
  (contains_record st s && get_key_at st s = k) 

(* convert a slot-indexed store to a key-indexed store *)
let rec as_map_aux (l:Seq.seq (option record)) : Tot V.vstore
  (decreases (Seq.length l)) =
  let n = Seq.length l in
  if n = 0 then fun _ -> None
  else 
    let l' = SA.prefix l (n - 1) in
    let f' = as_map_aux l' in
    match Seq.index l (n - 1) with
    | None -> f'
    | Some (Record k v a) -> 
      fun (k':key) -> if k = k' then Some (V.VStore v a) else f' k' 

let as_map (st:vstore{st.is_map}) : V.vstore =
  as_map_aux st.data

//let lemma_as_map_key_slot_equiv (st:vstore{st.is_map})
//  : Lemma (forall (k:key). ?? )
// key_slot_equiv st s k -> value at st s = value at (as_map st) k
