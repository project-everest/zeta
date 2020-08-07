module Veritas.State

open FStar.Seq
open Veritas.Interleave
open Veritas.Key
open Veritas.Record
open Veritas.SeqAux

type state_op = 
  | Get: k:data_key -> v:data_value -> state_op
  | Put: k:data_key -> v:data_value -> state_op

let is_get (o: state_op) = Get? o
let is_put (o: state_op) = Put? o

let is_get_idx (s: seq state_op) (i: seq_index s) = is_get (index s i)
let is_put_idx (s: seq state_op) (i: seq_index s) = is_put (index s i)

(* key of an operation *)
let key_of (o: state_op) = 
  match o with 
  | Get k _ -> k
  | Put k _ -> k

let key_of_idx (s: seq state_op) (i: seq_index s) = key_of (index s i)

let value_of (o: state_op) = 
  match o with
  | Get _ v -> v
  | Put _ v -> v

let value_of_idx (s: seq state_op) (i: seq_index s) = value_of (index s i)

let is_put_of_key (k: data_key) (o: state_op) = 
  match o with
  | Put k' _ -> k = k'
  | _ -> false

let has_some_put (s: seq state_op) (k: data_key) = 
  exists_sat_elems (is_put_of_key k) s

let last_put_idx (s: seq state_op) (k: data_key {has_some_put s k}) = 
  last_index (is_put_of_key k) s

let last_put_value_or_null (s: seq state_op) (k: data_key) = 
  if has_some_put s k then
     value_of (index s (last_put_idx s k))
  else
    Null

let rw_consistent_idx (s: seq state_op) (i: seq_index s) = 
  is_get_idx s i ==> value_of_idx s i = last_put_value_or_null (prefix s i) (key_of_idx s i) 

let rw_inconsistent_idx (s: seq state_op) (i: seq_index s) = 
  ~ (rw_consistent_idx s i)

(* read-write consistency (correctness) of a sequence of state operations *)
type rw_consistent (s: (seq state_op)) = forall (i:seq_index s). rw_consistent_idx s i
  
(* 
 * rw_consistency: computational version: determine if sequence is rw_consistent;
 * if it is not, return the smallest index causing inconsistency 
 *)
val eval_rw_consistency (s: seq (state_op)): 
  Tot (r:(bool * nat){(fst r <==> rw_consistent s) /\
                     (~(rw_consistent s) ==> (snd r < length s /\ 
                                             rw_inconsistent_idx s (snd r) /\
                                             rw_consistent (prefix s (snd r))))})

(* sequential consistency of a concurrent sequences of state operations *)
type seq_consistent (ss: seq (seq state_op)) = 
  exists s. interleave #state_op s ss /\ rw_consistent s
