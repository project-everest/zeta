module Veritas.Steel.Verifier
open Steel.Effect
open Steel.Effect.Atomic
open Steel.Memory
open Steel.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Veritas.Steel.VCache
open Veritas.Steel.Types
open Steel.Reference


module MSH = Veritas.MultiSetHashDomain
let model_hash = erased MSH.mset_ms_hashfn_dom

[@@erasable]
noeq
type thread_state_model = {
  model_failed : bool;
  model_store  : VCache.contents;
  model_clock  : erased U64.t;
  model_hadd   : model_hash;
  model_hevict : model_hash;
}

val prf_set_hash : Type0
val prf_set_hash_inv (_:prf_set_hash) (_:model_hash) : slprop u#1

let thread_id = U32.t
let counter_t = ref U64.t

noeq
type thread_state_t = {
  id           : thread_id;
  st           : vstore;  //a map from keys (cache ids) to merkle leaf or internal nodes
  clock        : counter_t;
  hadd         : prf_set_hash; //current incremental set hash values; TODO
  hevict       : prf_set_hash;
  failed       : ref bool
}

[@@__reduce__]
let thread_state_inv (t:thread_state_t) (m:thread_state_model)
  : slprop
  = VCache.is_vstore t.st m.model_store `star`
    //NS: it actually seems to matter that I associate it explicitly this way
    //which is odd. See failure in vget if you remove the parentheses
    (pts_to t.clock full_perm m.model_clock `star`
     (pts_to t.failed full_perm m.model_failed `star`
      (prf_set_hash_inv t.hadd m.model_hadd `star`
       prf_set_hash_inv t.hevict m.model_hevict)))

let change_slprop (#[@@framing_implicit] p:slprop)
                  (#[@@framing_implicit] q:slprop)
                  (_:unit)
  : Steel unit p (fun _ -> q) (requires fun _ -> p==q) (ensures fun _ _ _ -> True)
  = Steel.Effect.change_slprop p q (fun _ -> ())

val sladmit (#[@@framing_implicit] p:slprop)
            (#[@@framing_implicit] q:slprop)
            (_:unit)
  : SteelT unit p (fun _ -> q)

let model_fail tsm = {tsm with model_failed=false}

let fail (#tsm:_) (vs:thread_state_t) (msg:string)
  : SteelT unit
    (thread_state_inv vs tsm)
    (fun _ -> thread_state_inv vs (model_fail tsm))
  = let _ = Steel.Reference.write vs.failed false in ()

let slot (tsm:thread_state_model) = VCache.slot_id tsm.model_store

let vget_model tsm (s:slot tsm) (v:value) : thread_state_model =
  match Seq.index tsm.model_store (U32.v s) with
  | None -> model_fail tsm
  | Some r' ->
    if v = r'.record_value then tsm else model_fail tsm

let emp_unit (p:slprop)
  : Lemma ((p `star` emp == p) /\
           (emp `star` p == p))
          [SMTPatOr [[SMTPat (p `star` emp)];
                     [SMTPat (emp `star` p)]]]
  = admit()

let vget (#tsm:_) (s:slot tsm) (v:value) (vs: thread_state_t)
  : SteelT unit
    (requires thread_state_inv vs tsm)
    (ensures fun _ -> thread_state_inv vs (vget_model tsm s v))
  = let ro = VCache.vcache_get_record vs.st s in
    match ro with
    | None ->
      fail vs "Slot not found";
      rewrite_context ()
    | Some r' ->
      if v = r'.record_value
      then rewrite_context ()
      else (fail vs "Failed: inconsistent key or value in Get";
            rewrite_context ())

let model_get_record (tsm:thread_state_model) (s:slot tsm)
  : GTot (option record)
  = Seq.index tsm.model_store (U32.v s)

let model_put_record (tsm:thread_state_model) (s:slot tsm) (r:record)
  : thread_state_model
  = {tsm with model_store=Seq.upd tsm.model_store (U32.v s) (Some r)}

let model_evict_record (tsm:thread_state_model) (s:slot tsm)
  : thread_state_model
  = {tsm with model_store=Seq.upd tsm.model_store (U32.v s) None }

let vput_model (tsm:thread_state_model) (s:slot tsm) (v:value)
  : thread_state_model
  = match model_get_record tsm s with
    | None -> model_fail tsm
    | Some r -> model_put_record tsm s ({r with record_value=v})

(* verifier write operation *)
let vput (#tsm:_) (s:slot tsm) (v:value) (vs: thread_state_t)
  : SteelT unit
    (requires thread_state_inv vs tsm)
    (ensures fun _ -> thread_state_inv vs (vput_model tsm s v))
  = let ro = VCache.vcache_get_record vs.st s in
    match ro with
    | None ->
      let _ = fail #tsm vs "Slot not found" in
      //Same as in vcache_set, but this time we have emps on both sides
      rewrite_context ()

    | Some r ->
      let x = vcache_update_record vs.st s ({ r with record_value = v }) in
      rewrite_context #(is_vstore _ _ `star` (pts_to vs.clock _ _ `star` (pts_to vs.failed _ _ `star` _)))
                      #(thread_state_inv _ _)
                      ()

val epoch_of_timestamp (t:timestamp) : U32.t


val mk_mhdom (r:record) (t:timestamp) (thread_id:thread_id) : MSH.ms_hashfn_dom

val model_update_hash (h:model_hash) (r:record) (t:timestamp) (thread_id:thread_id)
  : model_hash

val prf_update_hash (#m:model_hash) (p:prf_set_hash) (r:record) (t:timestamp) (thread_id:thread_id)
  : SteelT unit
    (prf_set_hash_inv p m)
    (fun _ -> prf_set_hash_inv p (model_update_hash m r t thread_id))

let model_update_hadd (tsm:_) (r:record) (t:timestamp) (thread_id:thread_id) =
  ({tsm with model_hadd = model_update_hash tsm.model_hadd r t thread_id})

val update_hadd (#tsm:_) (r:record) (t:timestamp) (thread_id:thread_id) (vs:thread_state_t)
  : SteelT unit
    (thread_state_inv vs tsm)
    (fun _ -> thread_state_inv vs ({tsm with model_hadd = model_update_hash tsm.model_hadd r t thread_id})) //(model_update_hadd tsm r t thread_id))

let model_update_hevict (tsm:_) (r:record) (t:timestamp) (thread_id:thread_id) =
  ({tsm with model_hevict = model_update_hash tsm.model_hevict r t thread_id})

val update_hevict (#tsm:_) (r:record) (t:timestamp) (thread_id:thread_id) (vs:thread_state_t)
  : SteelT unit
    (thread_state_inv vs tsm)
    (fun _ -> thread_state_inv vs (model_update_hevict tsm r t thread_id))

open FStar.Integers

let model_update_clock (tsm:thread_state_model) (ts:timestamp)
  : thread_state_model
  = if FStar.UInt.fits (U64.v tsm.model_clock + U64.v ts) 64
    then { tsm with model_clock = tsm.model_clock + ts } //+1
    else model_fail tsm

let update_clock (#tsm:_) (ts:timestamp) (vs:thread_state_t)
  : SteelT unit
    (thread_state_inv vs tsm)
    (fun _ -> thread_state_inv vs (model_update_clock tsm ts))
  = sladmit()

let mk_record k v am = { record_key = k; record_value = v; record_add_method = am;
                         record_l_child_in_store = Vfalse;
                         record_r_child_in_store = Vfalse }

let vaddb_model (tsm:thread_state_model) (s:slot tsm) (r:record) (t:timestamp) (thread_id:thread_id)
  : thread_state_model
  = let e = epoch_of_timestamp t in
    let { record_key = k;
          record_value = v } = r in
    (* check value type consistent with key k *)
    if not (is_value_of k v) then model_fail tsm
    else if Some? (model_get_record tsm s) then model_fail tsm
    else (
      //TODO: need to check that the key does not exist
      (* updated h_add *)
      let tsm = model_update_hadd tsm r t thread_id in
      (* updated clock *)
      let tsm = model_update_clock tsm t in
      (* add record to store *)
      model_put_record tsm s (mk_record k v BAdd)
    )

let vaddb (#tsm:_)
          (s:slot tsm)
          (r:record)
          (t:timestamp)
          (thread_id:thread_id)
          (vs:thread_state_t)
  : SteelT unit
    (requires thread_state_inv vs tsm)
    (ensures fun _ -> thread_state_inv vs (vaddb_model tsm s r t thread_id))
  = (* epoch of timestamp of last evict *)
    let e = epoch_of_timestamp t in
    let { record_key = k;
          record_value = v } = r in
    (* check value type consistent with key k *)
    if not (is_value_of k v)
    then (
      fail vs "vaddm: value is incompatible with key";
      rewrite_context #(thread_state_inv vs _)
                      #(thread_state_inv vs _)
                      ()
    )
    else (
      let ro = VCache.vcache_get_record vs.st s in
      if Some? ro
      then (
        fail vs "vaddm: slot s already exists";
        rewrite_context #(thread_state_inv _ _)
                        #(thread_state_inv _ _)
                        ()
      )
      else (
        prf_update_hash vs.hadd r t thread_id;// vs;
        update_clock #(model_update_hadd tsm r t thread_id) t vs;
        //this next line is tricky for a couple of reasons
        // 1. the implicit arg to vcache_update_record is unified with the type of `s` which is indexed
        //    by the original tsm, not the current one
        // 2. the refinement type mk_record require `is_value_of k v` does not seem to be provable
        //    here. despite the check above.
        VCache.vcache_update_record #((model_update_clock _ _).model_store) vs.st s (mk_record k v BAdd);
        rewrite_context #(is_vstore _ _ `star` (pts_to vs.clock _ _ `star` (pts_to vs.failed _ _ `star` _)))
                        #(thread_state_inv vs (vaddb_model tsm s r t thread_id))
                        ()
      )
    )

let timestamp_lt (t0 t1:timestamp) = t0 `U64.lt` t1

let vevictb_model (tsm:thread_state_model) (s:slot tsm) (t:timestamp) (thread_id:thread_id)
  : GTot thread_state_model
  = let e = epoch_of_timestamp t in
    let clk = tsm.model_clock in
    if not (clk `timestamp_lt` t)
    then model_fail tsm
    else begin
      (* check that the vstore contains s *)
      match model_get_record tsm s with
      | None -> model_fail tsm
      | Some r ->
        (* update the evict hash *)
        let tsm = model_update_hevict tsm r t thread_id in
        (* advance clock to t *)
        let tsm = model_update_clock tsm t in
        (* evict record *)
        model_evict_record tsm s
    end

let read_id (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  : Steel a
    (requires pts_to r p v)
    (ensures fun _ -> pts_to r p v)
    (requires fun _ -> True)
    (ensures fun _ res _ -> hide res == v)
  = let x = read r in
    rewrite_context #(pts_to r p (hide x))
                    #(pts_to r p v)
                    ();
    x


let vevictb (#tsm:_)
            (s:slot tsm)
            (t:timestamp)
            (vs:thread_state_t)
  : SteelT unit
    (requires thread_state_inv vs tsm)
    (ensures fun _ -> thread_state_inv vs (vevictb_model tsm s t vs.id))
  = let clk = read_id vs.clock in
    if not (clk `timestamp_lt` t)
    then (
      fail vs "Timestamp is old";
      rewrite_context #(thread_state_inv _ _)
                      #(thread_state_inv _ _)
                       ()
    )
    else (
      (* check that the vstore contains s *)
      let r = VCache.vcache_get_record vs.st s in
      match r with
      | None ->
        fail vs "Slot is empty";
        rewrite_context #(thread_state_inv _ _)
                        #(thread_state_inv _ _)
                        ()

      | Some r ->
        (* update the evict hash *)
        prf_update_hash vs.hevict r t vs.id;

        update_clock #(model_update_hevict tsm r t vs.id) t vs;

        VCache.vcache_evict_record #((model_update_clock _ _).model_store) vs.st s;

        rewrite_context #(is_vstore _ _ `star` (pts_to vs.clock _ _ `star` (pts_to vs.failed _ _ `star` _)))
                        #(thread_state_inv vs (vevictb_model tsm s t vs.id))
                        ())

// let vevictbm (s s':slot_id) (t:timestamp) (vs:thread_state_t)
//   : StackExn unit
//     (requires fun h -> thread_state_inv vs h)
//     (ensures fun h0 _ h1 -> thread_state_inv vs h1)
//   = let r = vstore_get_record vs.st s in
//     let r' = vstore_get_record vs.st s' in
//     match is_descendent r.record_key r'.record_key with
//     | Some Eq
//     | None -> raise "vevictbm: Not a proper descendant"
//     | Some lr ->
//       assume (V_mval? r'.record_value);
//       let dh' = desc_hash_dir r'.record_value lr in
//       match dh' with
//       | Dh_vnone _ -> raise "vevictbm: parent entry is empty for this child"
//       | Dh_vsome ({ dhd_key = k2; dhd_h = h2; evicted_to_blum = b2 ;}) ->
//         if k2 = r.record_key && b2 = Vfalse then
//            let v'_upd = update_merkle_value r'.record_value lr (Dh_vsome ({ dhd_key = r.record_key; dhd_h = h2; evicted_to_blum = Vtrue; })) in
//            let r' = { r with record_value = v'_upd } in
//            vstore_update_record vs.st s' r';
//            vevictb s t vs
//         else raise "vevictbm: evicted to blum is already set in parent"
