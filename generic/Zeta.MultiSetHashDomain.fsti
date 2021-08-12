module Zeta.MultiSetHashDomain

open FStar.BitVector
open Zeta.App
open Zeta.Key
open Zeta.MultiSet
open Zeta.Record
open Zeta.Thread
open Zeta.Time

type ms_hashfn_dom (aprm: app_params) =
  | MHDom: r:record aprm -> t:timestamp -> tid:thread_id -> ms_hashfn_dom aprm

val ms_hashfn_dom_cmp (aprm: app_params)
  : cmp (ms_hashfn_dom aprm)

type mset_ms_hashfn_dom (aprm: app_params) = mset (ms_hashfn_dom aprm) (ms_hashfn_dom_cmp aprm)

let epoch_of #aprm (e: ms_hashfn_dom aprm) =
  let MkTimestamp e _ = e.t in
  e
