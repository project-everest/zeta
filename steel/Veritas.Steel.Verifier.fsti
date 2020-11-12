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
let thread_id = U32.t
let counter_t = ref U64.t
val prf_set_hash : Type0
val prf_set_hash_inv (_:prf_set_hash) : slprop u#1

noeq
type thread_state_t = {
  id           : thread_id;
  st           : vstore;  //a map from keys (cache ids) to merkle leaf or internal nodes
  clock        : counter_t;
  hadd         : prf_set_hash; //current incremental set hash values; TODO
  hevict       : prf_set_hash;
  failed       : ref bool
}

[@@erasable]
noeq
type thread_state_model = {
  model_failed : bool;
  model_store : VCache.contents;
  model_clock : erased U64.t;
//add sets to model hash state
}

[@@__reduce__]
let thread_state_inv (t:thread_state_t) (m:thread_state_model)
  : slprop
  = VCache.is_vstore t.st m.model_store `star`
    pts_to t.clock full_perm m.model_clock `star`
    pts_to t.failed full_perm m.model_failed

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

let vget (#tsm:_) (s:slot tsm) (v:value) (vs: thread_state_t)
  : SteelT unit
    (requires thread_state_inv vs tsm)
    (ensures fun _ -> thread_state_inv vs (vget_model tsm s v))
  = let ro = VCache.vcache_get_record vs.st s in
    match ro with
    | None ->
      fail vs "Slot not found";
      change_slprop ()
    | Some r' ->
      if v = r'.record_value
      then (change_slprop #(thread_state_inv vs tsm) #(thread_state_inv vs (vget_model tsm s v)) (); ())
      else (fail vs "Failed: inconsistent key or value in Get";
            change_slprop())

let model_get_record (tsm:thread_state_model) (s:slot tsm)
  : GTot (option record)
  = Seq.index tsm.model_store (U32.v s)

let model_put_record (tsm:thread_state_model) (s:slot tsm) (r:record)
  : thread_state_model
  = {tsm with model_store=Seq.upd tsm.model_store (U32.v s) (Some r)}

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
      let _ = fail vs "Slot not found" in
      change_slprop()

    | Some r ->
      let x = vcache_update_record vs.st s ({ r with record_value = v }) in
      change_slprop #(is_vstore _ _ `star` pts_to vs.clock _ _ `star` pts_to vs.failed _ _)// (Mkthread_state_t?.st vs)
                      //           (hide (Seq.Base.upd (reveal (Mkthread_state_model?.model_store tsm))
                      //                               (UInt32.v s)
                      //                               (Some (update_record_value r v)))) `star`
                      // Steel.Reference.pts_to (Mkthread_state_t?.clock vs)
                      //                        full_perm
                      //                        (Mkthread_state_model?.model_clock tsm))
                    #(thread_state_inv vs (vput_model tsm s v))
                    ()

val epoch_of_timestamp (t:timestamp) : U32.t

val model_update_hash (tsm:thread_state_model) (r:record) (t:timestamp) (thread_id:thread_id)
  : tsm':thread_state_model{tsm.model_store == tsm'.model_store}
val update_hash (#tsm:_) (r:record) (t:timestamp) (thread_id:thread_id) (vs:thread_state_t)
  : SteelT unit
    (thread_state_inv vs tsm)
    (fun _ -> thread_state_inv vs (model_update_hash tsm r t thread_id))

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
      let tsm = model_update_hash tsm r t thread_id in
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
      change_slprop #(thread_state_inv vs _)
                    #(thread_state_inv vs _)
                    ()
    )
    else (
      let ro = VCache.vcache_get_record vs.st s in
      if Some? ro
      then (
        fail vs "vaddm: slot s already exists";
        change_slprop #(thread_state_inv _ _)
                      #(thread_state_inv _ _)
                      ()
      )
      else (
        update_hash r t thread_id vs;
        update_clock t vs;
        //this next line is tricky for a couple of reasons
        // 1. the implicit arg to vcache_update_record is unified with the type of `s` which is indexed
        //    by the original tsm, not the current one
        // 2. the refinement type mk_record require `is_value_of k v` does not seem to be provable
        //    here. despite the check above.
        VCache.vcache_update_record #((model_update_clock _ _).model_store) vs.st s (mk_record k v BAdd);
        change_slprop #(is_vstore _ _ `star` pts_to vs.clock _ _ `star` pts_to vs.failed _ _)
                      #(thread_state_inv vs (vaddb_model tsm s r t thread_id))
                      ()
      )
    )

// let vevictb (s:slot_id) (t:timestamp) (vs:thread_state_t)
//   : StackExn unit
//     (requires fun h -> thread_state_inv vs h)
//     (ensures fun h0 _ h1 -> thread_state_inv vs h1)
//   = let e = epoch_of_timestamp in
//     let clk = B.index vs.clock 0ul in
//     if not (clk `timestamp_lt` t) then raise "vevictb: timestamp does not exceed the clock";
//     (* check that the vstore contains s *)
//     let r = vstore_get_record vs.st s in
//     (* update the evict hash *)
//     multiset_hash_upd r t vs.id vs.hevict;
//     (* advance clock to t *)
//     update_clock t vs.clock;
//     (* evict record *)
//     vstore_evict_record vs.st s r.record_key

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
