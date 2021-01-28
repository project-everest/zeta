module Veritas.Steel.VCache
open Steel.Effect
open Steel.Memory
open Steel.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32
open Steel.Array
open Veritas.Steel.Types

let is_value_of (k:key) (v:value) = admit()
let is_data_key (k:key) : bool = admit()

let vstore  = Steel.Array.array (option record)

[@@__reduce__]
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

let vcache_create n =
  let a = Steel.Array.alloc None n in
  // // This didn't work
  // rewrite_context();
  // a
  rewrite_context #(Steel.Array.is_array _ _ _) #(is_vstore _ _) ();
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
    //without the implicit below, rewrite_context aims to prove at `is_array _ _ _ * emp == is_array _ _ _`
    //which the SMT solver can't do
    //providing the implicit below, focuses the rewrite_context
    rewrite_context #(is_array _ _ _) ()
