module Veritas.LowLevelVerifier
open FStar.Integers
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack

open LowStar.Exception
module VStore = Veritas.VCache
open Veritas.VCache


let thread_id_t = uint_16
let counter_t = B.pointer uint_64
let timestamp = uint_64
assume
val timestamp_lt (t1 t2: timestamp) : bool

let max (t1 t2: timestamp) =
  if t1 `timestamp_lt` t2 then t2 else t1

let epoch_of_timestamp (t:timestamp)
  : uint_64
  = admit()

let vstore = Veritas.VCache.vstore

assume
val prf_set_hash : Type0
assume
val prf_set_hash_loc (v:prf_set_hash) : B.loc
assume
val prf_set_hash_inv (v:prf_set_hash) (h:HS.mem) : Type
assume
val prf_set_hash_inv_framing (v:prf_set_hash) (h0 h1:HS.mem) (l:B.loc)
  : Lemma (ensures
             prf_set_hash_inv v h0 /\
             B.modifies l h0 h1 /\
             B.loc_disjoint l (prf_set_hash_loc v) ==>
             prf_set_hash_inv v h1)
          [SMTPat (prf_set_hash_inv v h1);
           SMTPat (B.modifies l h0 h1)]

assume
val multiset_hash_upd (r:record) (t:timestamp) (j:thread_id_t) (v:prf_set_hash)
  : Stack unit
    (requires fun h -> prf_set_hash_inv v h)
    (ensures fun h0 _ h1 ->
      prf_set_hash_inv v h1 /\
      B.modifies (prf_set_hash_loc v) h0 h1)

assume
val get_current_value   (v:prf_set_hash)
  : Stack u256
    (requires fun h -> prf_set_hash_inv v h)
    (ensures fun h0 _ h1 -> h0 == h1)

noeq
type thread_state_t = {
  id           : thread_id_t;
  st           : vstore;  //a map from keys (cache ids) to merkle leaf or internal nodes
  clock        : counter_t;
  hadd         : prf_set_hash; //current incremental set hash values; TODO
  hevict       : prf_set_hash;
}


let thread_state_inv (t:thread_state_t) (h:HS.mem)
  = VStore.invariant t.st h /\
    prf_set_hash_inv t.hadd h /\
    prf_set_hash_inv t.hevict h /\
    B.live h t.clock /\
    B.loc_disjoint (VStore.footprint t.st)
                   (B.loc_union (B.loc_buffer t.clock)
                     (B.loc_union (prf_set_hash_loc t.hadd)
                                  (prf_set_hash_loc t.hevict))) /\
    B.loc_disjoint (B.loc_buffer t.clock)
                   (B.loc_union (prf_set_hash_loc t.hadd)
                                (prf_set_hash_loc t.hevict)) /\
    B.loc_disjoint (prf_set_hash_loc t.hadd)
                   (prf_set_hash_loc t.hevict)
    (* /\ ... *)
let loc_thread_state (t:thread_state_t) =
    B.loc_union (VStore.footprint t.st)
                   (B.loc_union (B.loc_buffer t.clock)
                     (B.loc_union (prf_set_hash_loc t.hadd)
                                  (prf_set_hash_loc t.hevict)))

////////////////////////////////////////////////////////////////////////////////

type desc_type =
  | Left
  | Right
  | Eq

let desc_type_lr = d:desc_type { Left? d \/ Right? d}

assume
val is_descendent (k0 k1:key)
  : option desc_type

let data_key   = k:key { is_data_key k }
let merkle_key = k:key { not (is_data_key k) }

let mvalue = v:value{ MVal? v }
let dvalue = v:value{ DVal? v }

val compute_hash (d:value)
  : Stack hash_value
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> B.modifies B.loc_none h0 h1)

assume val serialize_length: value -> l:UInt32.t { UInt32.v l > 0 }

assume val serialize_value: v:value -> dst: B.lbuffer UInt8.t (UInt32.v (serialize_length v)) ->
  Stack unit
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> B.(modifies (loc_buffer dst) h0 h1))

let compute_hash d =
  Veritas.Reveal.reveal_u8 ();
  assert_norm (8 <= Spec.Hash.Definitions.max_input_length Spec.Hash.Definitions.SHA2_256);
  assert_norm (pow2 32 < pow2 61);
  push_frame ();
  let l = serialize_length d in
  let tmp = B.alloca 0uy l in
  serialize_value d tmp;
  let hash = B.alloca 0uy 32ul in
  Hacl.Hash.SHA2.hash_256 tmp l hash;
  let hash0 = B.sub hash 0ul 8ul in
  let hash1 = B.sub hash 8ul 8ul in
  let hash2 = B.sub hash 16ul 8ul in
  let hash3 = B.sub hash 24ul 8ul in
  let r =
    LowStar.Endianness.load64_le hash0,
    LowStar.Endianness.load64_le hash1,
    LowStar.Endianness.load64_le hash2,
    LowStar.Endianness.load64_le hash3
  in
  pop_frame ();
  r

let vstore_try_get_record (v:vstore) (s:slot_id)
  : Stack (option record)
    (requires fun h -> VStore.invariant v h)
    (ensures fun h0 r h1 -> h0 == h1 (* /\ r = h0.v.entries s *))
  = VStore.vcache_get_record v s

let vstore_get_record (v:vstore) (s:slot_id)
  : StackExn record
    (requires fun h -> VStore.invariant v h)
    (ensures fun h0 r h1 -> h0 == h1 (* /\ r = h0.v.entries s *))
  = match vstore_try_get_record v s with
    | None -> raise "vstore does not contain slot"
    | Some r -> r

let vstore_update_record (v:vstore) (s:slot_id) (r:record)
  : Stack unit
    (requires fun h -> VStore.invariant v h)
    (ensures fun h0 _ h1 ->
      VStore.invariant v h1 /\
      B.modifies (VStore.footprint v) h0 h1)
      // h1.v.entries == upd h0.v.entries s r
  = VStore.vcache_update_record v s r

let vstore_add_record (v:vstore) (s:slot_id) (k:key) (vk:value{is_value_of k vk}) (a:add_method)
  : Stack unit
    (requires fun h -> VStore.invariant v h)
    (ensures fun h0 _ h1 ->
      VStore.invariant v h1 /\
      B.modifies (VStore.footprint v) h0 h1
      // h1.v.entries == upd h0.v.entries s r
    )
  = VStore.vcache_add_record v s k vk a

let vstore_evict_record (v:vstore) (s:slot_id) (k:key)
  : Stack unit
    (requires fun h -> VStore.invariant v h)
    (ensures fun h0 _ h1 ->
      VStore.invariant v h1 /\
      B.modifies (VStore.footprint v) h0 h1 // /\
      // h1.v.entries == upd h0.v.entries s r
    )
  = VStore.vcache_evict_record v s k

let vget (s:slot_id) (v:data_value) (vs: thread_state_t)
  : StackExn unit
    (requires fun h -> thread_state_inv vs h)
    (ensures fun h0 _ h1 -> h0 == h1)
  = let r = vstore_get_record vs.st s in
    match r.record_value with
    | MVal _ _ ->
      raise "expected a data value"
    | DVal dv ->
      if dv = v
      then ()
      else raise "Failed: inconsistent key or value in Get"

(* verifier write operation *)
let vput (s:slot_id) (v:data_value) (vs: thread_state_t)
  : StackExn unit
    (requires fun h -> thread_state_inv vs h)
    (ensures fun h0 _ h1 ->
      thread_state_inv vs h1)
  = let r = vstore_get_record vs.st s in
    vstore_update_record vs.st s ({r with record_value = DVal v})

(* update merkle value *)
let update_merkle_value (v:value{MVal? v})
                        (d:desc_type_lr)
                        (dh:descendent_hash)
  : v:value{MVal? v}
  = let MVal dhl dhr = v in
    match d with
    | Left -> MVal dh dhr
    | Right -> MVal dhl dh

unfold
let with_in_store_direction r (d:desc_type_lr) (flag:bool)
  : record
  = match d with
    | Left -> {r with record_l_child_in_store = flag}
    | Right -> {r with record_r_child_in_store = flag}

let init_value (k:key): v:value{is_value_of k v} =
  if is_data_key k then DVal None
  else MVal Empty Empty

let vaddm (s:slot_id)
          (r:record)
          (s':slot_id)
          (vs: thread_state_t)
  : StackExn unit
    (requires fun h -> thread_state_inv vs h)
    (ensures fun h0 _ h1 -> thread_state_inv vs h1)
  = let { record_key = k; record_value = v } = r in
    (* check k is a proper desc of k' and that k is not already in the store *)
    let {
          record_key = k';
          record_value = mv;
          record_l_child_in_store = l_in_store;
          record_r_child_in_store = r_in_store;
          record_add_method = add_method'
        } = vstore_get_record vs.st s'
    in
    let direction, mval, desc_hash_dir
      : desc_type_lr & mvalue & descendent_hash
      = match mv with
        | DVal _ -> raise "vaddm: expected merkle slot, got data slot"
        | MVal l r ->
          match is_descendent k k' with
          | Some Left ->
            if Desc? l && l_in_store
            then raise "vaddm: key is already in the store"
            else Left, mv, l
          | Some Right ->
            if Desc? r && r_in_store
            then raise "vaddm: key is already in the store"
            else Right, mv, r
          | _ -> raise "vaddm: not a proper descendant"
    in
    (* check store does not contain k *)
    (match vstore_try_get_record vs.st s with
     | None -> ()
     | Some _ -> raise "slot s already exists");
    (* check that type of value is consistent with key *)
    if not (is_value_of k v) then raise "vaddm: value is not consistent for key";
    let h = compute_hash v in
    match desc_hash_dir with
    | Empty ->
      if v <> init_value k then raise "vaddm: First add expected initial value";
      let dh = Desc k h false in
      let mval' = update_merkle_value mval direction dh in
      vstore_update_record vs.st s' (mk_record k' mval' add_method');
      vstore_add_record vs.st s k v MAdd

    | Desc k2 h2 k2_in_blum ->
      if k2 = k then
         if h2 = h then
            vstore_add_record vs.st s k v MAdd //TODO: Need to update s' in_store bit for s
         else raise "vaddm: adding existing merkle node to store, but hash does not match"
      else if v <> init_value k then raise "vaddm: new node, expected initial value"
      else match is_descendent k2 k with
           | None
           | Some Eq -> raise "vaddm: existing edge in merkle tree is not for a proper descendent of k"
           | Some lr ->
             assume (MVal? v); //k has a strict descendent, so it cannot be a data key
             let mv_upd = update_merkle_value v lr desc_hash_dir in
             let mval' = update_merkle_value mval direction (Desc k h false) in
             vstore_update_record vs.st s' (with_in_store_direction (mk_record k' mval' add_method') direction true);
             vstore_add_record vs.st s k mv_upd MAdd

let desc_hash_dir (v:mvalue) (lr:desc_type_lr)
  : descendent_hash
  = match lr with
    | Left -> MVal?.l v
    | Right -> MVal?.r v

let vevictm (s:slot_id)
            (s':slot_id)
            (vs: thread_state_t)
  : StackExn unit
    (requires fun h -> thread_state_inv vs h)
    (ensures fun h0 _ h1 -> thread_state_inv vs h1)
  = let {
          record_key = k;
          record_value = v;
        } = vstore_get_record vs.st s
    in
    let {
          record_key = k';
          record_value = v';
          record_add_method = a'
        } = vstore_get_record vs.st s'
    in
     match is_descendent k k' with
    | None
    | Some Eq -> raise "vevictm: expected a proper descendant"
    | Some lr ->
      assume (MVal? v'); //k' has a strict descendant
      let dh' = desc_hash_dir v' lr in
      let h = compute_hash v in
      match dh' with
      | Empty ->
        raise "vevictm: Evicting child node should be in the merkle tree"
      | Desc k2 h2 b2 ->
        if k2 = k then
        begin
           vstore_evict_record vs.st s k; //evict s, k first
           //then update parent with in_store bit = false
           let v'_upd = update_merkle_value v' lr (Desc k h b2) in
           vstore_update_record vs.st s' (with_in_store_direction (mk_record k' v'_upd a') lr false)
        end

let update_clock (t:timestamp) (clk:counter_t)
  : Stack unit
    (requires fun h -> B.live h clk)
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_buffer clk) h0 h1 /\
      B.live h1 clk /\
      B.get h1 clk 0 = max (B.get h0 clk 0) t)
  = let c0 = B.index clk 0ul in
    B.upd clk 0ul (max c0 t)

let vaddb (s:slot_id)
          (r:record)
          (t:timestamp)
          (thread_id:thread_id_t)
          (vs:thread_state_t)
  : StackExn unit
    (requires fun h -> thread_state_inv vs h)
    (ensures fun h0 _ h1 -> thread_state_inv vs h1)
  = (* epoch of timestamp of last evict *)
    let e = epoch_of_timestamp t in
    let { record_key = k;
          record_value = v } = r in
    (* check value type consistent with key k *)
    if not (is_value_of k v) then raise "vaddm: value is incompatible with key";
    if Some? (vstore_try_get_record vs.st s) then raise "vaddm: slot s already exists";
    //TODO: need to check that the key does not exist
    (* updated h_add *)
    multiset_hash_upd r t thread_id vs.hadd;
    (* updated clock *)
    update_clock t vs.clock;
    (* add record to store *)
    vcache_add_record vs.st s k v BAdd

let vevictb (s:slot_id) (t:timestamp) (vs:thread_state_t)
  : StackExn unit
    (requires fun h -> thread_state_inv vs h)
    (ensures fun h0 _ h1 -> thread_state_inv vs h1)
  = let e = epoch_of_timestamp in
    let clk = B.index vs.clock 0ul in
    if not (clk `timestamp_lt` t) then raise "vevictb: timestamp does not exceed the clock";
    (* check that the vstore contains s *)
    let r = vstore_get_record vs.st s in
    (* update the evict hash *)
    multiset_hash_upd r t vs.id vs.hevict;
    (* advance clock to t *)
    update_clock t vs.clock;
    (* evict record *)
    vstore_evict_record vs.st s r.record_key

let vevictbm (s s':slot_id) (t:timestamp) (vs:thread_state_t)
  : StackExn unit
    (requires fun h -> thread_state_inv vs h)
    (ensures fun h0 _ h1 -> thread_state_inv vs h1)
  = let r = vstore_get_record vs.st s in
    let r' = vstore_get_record vs.st s' in
    match is_descendent r.record_key r'.record_key with
    | Some Eq
    | None -> raise "vevictbm: Not a proper descendant"
    | Some lr ->
      assume (MVal? r'.record_value);
      let dh' = desc_hash_dir r'.record_value lr in
      match dh' with
      | Empty -> raise "vevictbm: parent entry is empty for this child"
      | Desc k2 h2 b2 ->
        if k2 = r.record_key && b2 = false then
           let v'_upd = update_merkle_value r'.record_value lr (Desc r.record_key h2 true) in
           let r' = { r with record_value = v'_upd } in
           vstore_update_record vs.st s' r';
           vevictb s t vs
        else raise "vevictbm: evicted to blum is already set in parent"


////////////////////////////////////////////////////////////////////////////////
(* Each entry of the verifier log *)
noeq
type vlog_entry =
  | Get:     s:slot_id ->
             v:data_value ->
             vlog_entry
  | Put:     s:slot_id ->
             v:data_value ->
             vlog_entry
  | AddM:    s:slot_id ->
             r:record ->
             s':slot_id ->
             vlog_entry
  | EvictM:  s:slot_id ->
             s':slot_id ->
             vlog_entry
  | AddB:    s:slot_id ->
             r:record ->
             t:timestamp ->
             j:thread_id_t ->
             vlog_entry
  | EvictB:  s:slot_id ->
             t:timestamp ->
             vlog_entry
  | EvictBM: s:slot_id ->
             s':slot_id ->
             t:timestamp ->
             vlog_entry


noeq
type log = {
  len : uint_32;
  buf : B.lbuffer uint_8 (v len);
  pos : B.pointer (x:uint_32{v x <= v len})
}

let loc_log (l:log) = B.loc_union (B.loc_buffer l.buf) (B.loc_buffer l.pos)

let log_inv (l:log) (h:HS.mem) =
  B.live h l.buf /\
  B.live h l.pos /\
  B.disjoint l.buf l.pos

assume
val extract_log_entry (l:log)
  : Stack vlog_entry
          (requires fun h ->
            log_inv l h)
          (ensures fun h0 v h1 ->
            log_inv l h1 /\
            B.modifies (loc_log l) h0 h1) (* /\
            log at position h0.pos contains a vali repr of v *)

let has_more (l:log)
  : Stack bool
    (requires log_inv l)
    (ensures fun h0 b h1 -> h0 == h1)
  = B.index l.pos 0ul = l.len

noeq
type v_context = {
  log_stream : log;      //A custom allocator of uint64_t* blocks
  thread_state : thread_state_t;
  valid : bool
}

let v_context_inv (vs:v_context) (h:HS.mem) =
  thread_state_inv vs.thread_state h /\
  log_inv vs.log_stream h /\
  B.loc_disjoint
    (loc_log vs.log_stream)
    (loc_thread_state vs.thread_state)

let t_verify_step (vs:v_context)
  : StackExn unit
    (requires fun h ->
      v_context_inv vs h)
    (ensures fun h0 _ h1 ->
      v_context_inv vs h1)
  = let entry = extract_log_entry vs.log_stream in
    match entry with
    | Get s v ->
      vget s v vs.thread_state
    | Put s v ->
      vput s v vs.thread_state
    | AddM s r s' ->
      vaddm s r s' vs.thread_state
    | EvictM s s' ->
      vevictm s s' vs.thread_state
    | AddB s r t j ->
      vaddb s r t j vs.thread_state
    | EvictB s t ->
      vevictb s t vs.thread_state
    | EvictBM s s' t ->
      vevictbm s s' t vs.thread_state

let rec t_verify (vs:v_context)
  : StackExn unit
    (requires fun h ->
      v_context_inv vs h)
    (ensures fun h0 _ h1 ->
      v_context_inv vs h1)
  = if has_more vs.log_stream
    then (t_verify_step vs; t_verify vs)
