module Veritas.Steel.VCache
open Steel.Effect
open Steel.Memory
open Steel.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32
open Steel.Array

let key = nat
let value = nat
type add_method =
  | AddMerkle | AddBlum
let is_value_of (k:key) (v:value) = true
type record = {
  record_key : key;
  record_value : (v:value {is_value_of record_key v});
  record_add_method : add_method;
  record_l_child_in_store : bool;
  record_r_child_in_store : bool
}
let mk_record k v a = {
  record_key = k;
  record_value = v;
  record_add_method = a;
  record_l_child_in_store = false;
  record_r_child_in_store = false;
}
let most_significant_bit (k:key) : bool = false

let vstore  = Steel.Array.array (option record)
let is_vstore (st:vstore) (c:contents) : slprop u#1 =
  Steel.Array.is_array st (full_perm (Seq.length c)) c


let change_slprop (#[@@framing_implicit] p:slprop)
                  (#[@@framing_implicit] q:slprop)
                  (_:unit)
  : Steel unit p (fun _ -> q) (requires fun _ -> p==q) (ensures fun _ _ _ -> True)
  = Steel.Effect.change_slprop p q (fun _ -> ())

let change_slprop_ret (#a:Type)
                      (#[@@framing_implicit] p:a -> slprop)
                      (#[@@framing_implicit] q:a -> slprop)
                      (x:a)
  : Steel a (p x) (fun x -> q x) (requires fun _ -> p x == q x) (ensures fun _ _ _ -> True)
  = Steel.Effect.change_slprop (p x) (q x) (fun _ -> ()); x

let vcache_create _ n =
  let a = Steel.Array.alloc None n in
  // // This didn't work
  // let x = change_slprop_ret a in
  // x
  change_slprop #(Steel.Array.is_array _ _ _) #(is_vstore _ _) ();
  a

let vcache_get_record (#c:contents) (vst:vstore) (s:slot_id c)
  : Steel (option record)
          (is_vstore vst c)
          (fun _ -> is_vstore vst c)
          (fun _ -> True)
          (fun _ res _ -> res == Seq.index c (U32.v s))
  = read vst s

let vcache_set (#c:contents) (st:vstore) (s:slot_id c) (r:option record)
  : SteelT unit
      (is_vstore st c)
      (fun _ -> is_vstore st (Seq.upd c (U32.v s) r))
  = write st s r;
    change_slprop ()
