module Veritas.Intermediate.Verifier
open FStar.Integers
open Veritas.Intermediate.Common
module S = Veritas.Intermediate.Store
module MH = Veritas.MultiSetHash
open Veritas.Record
open Veritas.Key

noeq
type vtls =
  | Failed : vtls
  | Valid :
    id : thread_id_t ->
    st : S.vstore ->
    clock : timestamp ->
    hadd : MH.ms_hash_value ->
    hevict : MH.ms_hash_value ->
    vtls


let thread_store (vs:vtls { Valid? vs } )
  : S.vstore
  = Valid?.st vs

let vget (s:slot_id) (v:data_value) (vs: vtls {Valid? vs}): vtls =
  let st = thread_store vs in
  (* check store contains key *)
  if not (S.store_contains st s) then Failed
  (* check stored value is v *)
  else let Some r = S.get_record st s in
       if not (DVal? r.record_value)
       then Failed
       else if to_data_value r.record_value <> v
       then Failed
       else vs
