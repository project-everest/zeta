module Zeta.Steel.MultiSetHash

(* This module defines the abstraction of multi-set hashing and relates it to Zeta.Steel.HashAccumulator *)

open Zeta.Steel.HashAccumulator
open Zeta.Steel.Rel

module AT = Zeta.Steel.ApplicationTypes
module MS = Zeta.MultiSet
module MSD = Zeta.MultiSetHashDomain
module TSM = Zeta.Steel.ThreadStateModel

let app = AT.aprm

(* multist domain *)
type s_dom = {
  r: s_record;
  t: s_timestamp;
  tid: s_tid;
}

(* multiset domain - spec level *)
let i_dom = MSD.ms_hashfn_dom app

let related_msdom (s: s_dom) (i: i_dom)
  = let MSD.MHDom r t j = i in
    related_record s.r r /\
    related_timestamp s.t t /\
    related_tid s.tid j

(* total ordering for mset_dom *)
let mset_cmp = MSD.ms_hashfn_dom_cmp app

(* the type of multisets we are interested in *)
let mset = MSD.mset_ms_hashfn_dom app

let empty = MS.empty #i_dom #mset_cmp

(* multiset hash function *)
val ms_hashfn (ms: mset)
  : hash_value_t

val lemma_hashfn_empty (_:unit)
  : Lemma (ensures (ms_hashfn empty = initial_hash))

(* adding a new element to a multiset is equivalent to hash_accumulation in the hash domain *)
val lemma_update  (ms: mset) (ie: i_dom) (se: s_dom {related_msdom se ie})
  : Lemma (ensures (let h = ms_hashfn ms in
                    let ms' = MS.add_elem ms ie in
                    let h' = ms_hashfn ms' in
                    h' = TSM.update_hash_value h se.r se.t se.tid))

(* multiset hash of the union of two multisets is the aggregate hash of their hashes *)
val lemma_union (ms1 ms2: mset)
  : Lemma (ensures (let ms = MS.union ms1 ms2 in
                    let h1 = ms_hashfn ms1 in
                    let h2 = ms_hashfn ms2 in
                    let h = ms_hashfn ms in
                    h = aggregate_hashes h1 h2))

noeq type ms_hash_collision =
  | MSCollision: s1: mset ->
                 s2: mset {ms_hashfn s1 = ms_hashfn s2 /\ ~ (s1 == s2)} ->
                 ms_hash_collision
