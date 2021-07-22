module Veritas.MultiSetHashDomain

open FStar.BitVector
open FStar.Seq
open Veritas.Key
open Veritas.MultiSet
open Veritas.Record
open Veritas.SeqAux

(* size of a multiset hash value *)
let ms_hash_size = 256

(* multiset hash value *)
let ms_hash_value = bv_t ms_hash_size

(* Hash value of an empty set *)
val empty_hash_value: ms_hash_value

let epoch = nat

(* timestamp for blum *)
type timestamp =
  | MkTimestamp: e: epoch -> c: nat -> timestamp

let next (t: timestamp): timestamp =
  match t with
  | MkTimestamp e c -> MkTimestamp e (c + 1)

let ts_lt (t1 t2: timestamp) =
  let e1 = MkTimestamp?.e t1 in
  let c1 = MkTimestamp?.c t1 in
  let e2 = MkTimestamp?.e t2 in
  let c2 = MkTimestamp?.c t2 in
  e1 < e2 || e1 = e2 && c1 < c2

let ts_geq (t1 t2: timestamp) =
  not (ts_lt t1 t2)

let ts_leq (t1 t2: timestamp) =
  t1 = t2 || t1 `ts_lt` t2

let ts_gt (t1 t2: timestamp): bool =
  not (t1 `ts_leq` t2)

type ms_hashfn_dom =
  | MHDom: r:record -> t:timestamp -> i:nat -> ms_hashfn_dom

val ms_hashfn_dom_cmp
  : cmp ms_hashfn_dom

type mset_ms_hashfn_dom = mset ms_hashfn_dom ms_hashfn_dom_cmp

let key_of (e:ms_hashfn_dom): key =
  match e with
  | MHDom (k,_) _ _ -> k

let thread_id_of (e:ms_hashfn_dom): nat =
  match e with
  | MHDom _ _ tid -> tid

let is_of_thread_id (tid:nat) (e:ms_hashfn_dom): bool =
  thread_id_of e = tid

let timestamp_of (e:ms_hashfn_dom): timestamp =
  match e with
  | MHDom _ t _ -> t

let epoch_of e =
  match e with
  | MHDom _ (MkTimestamp e _) _ -> e
