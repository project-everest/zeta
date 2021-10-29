module Zeta.Steel.VCache

open Steel.Memory
open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open FStar.Ghost
module U16 = FStar.UInt16
module U32 = FStar.UInt32
open Steel.Array

module T = Zeta.Formats.Types
open Zeta.Steel.VerifierModel
module VM = Zeta.ThreadStateModel

let vstore (n:U16.t)
  : Type0
  = a:Steel.Array.array (option (VM.record n)) {
         U16.v n == Steel.Array.length a
    }

unfold
let is_vstore (#n:U16.t) (st:vstore n) = varray st

val vcache_create (n:U16.t)
  : Steel (vstore n)
           emp
           (fun v -> is_vstore v)
           (requires fun _ -> True)
           (ensures fun _ v h1 -> asel v h1 == Seq.create (U16.v n) None)


val free (#n:_) (p:vstore n)
  : SteelT unit
    (is_vstore p)
    (fun _ -> emp)

let slot (n:U16.t) = x:U16.t{ U16.v x < U16.v n }

val vcache_get_record (#n:_) (vst:vstore n) (s:slot n)
  : Steel (option (VM.record n))
          (is_vstore vst)
          (fun _ -> is_vstore vst)
          (requires fun h -> True)
          (ensures fun h0 res h1 ->
             asel vst h0 == asel vst h1 /\
             res == Seq.index (asel vst h1) (U16.v s))

val vcache_set (#n:_) (st:vstore n) (s:slot n) (r:option (VM.record n))
  : Steel unit
      (is_vstore st)
      (fun _ -> is_vstore st)
      (requires fun h -> True)
      (ensures fun h0 _ h1 ->
        asel st h1 == Seq.upd (asel st h0) (U16.v s) r)

let vcache_update_record (#n:_) (st:vstore n) (s:slot n) (r:VM.record n)
  : Steel unit
      (is_vstore st)
      (fun _ -> is_vstore st)
      (requires fun h -> True)
      (ensures fun h0 _ h1 ->
        asel st h1 == Seq.upd (asel st h0) (U16.v s) (Some r))
  = vcache_set st s (Some r)

let vcache_add_record
      (#n:_)
      (vst:vstore n)
      (s:slot n)
      (k:T.key)
      (v:T.value{VM.is_value_of k v})
      (a:T.add_method)
  : Steel unit
      (is_vstore vst)
      (fun _ -> is_vstore vst)
      (requires fun h -> True)
      (ensures fun h0 _ h1 ->
        asel vst h1 == Seq.upd (asel vst h0) (U16.v s) (Some (mk_record k v a)))
  = vcache_update_record vst s (mk_record k v a)

let vcache_evict_record
      (#n:_)
      (vst:vstore n)
      (s:slot n)
  : Steel unit
      (is_vstore vst)
      (fun _ -> is_vstore vst)
      (requires fun h -> True)
      (ensures fun h0 _ h1 ->
        asel vst h1 == Seq.upd (asel vst h0) (U16.v s) None)
  = vcache_set vst s None
