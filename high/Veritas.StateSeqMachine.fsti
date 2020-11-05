module Veritas.StateSeqMachine

open FStar.Seq
open Veritas.Record
open Veritas.SeqAux
open Veritas.State
open Veritas.SeqMachine

type ssm_state = 
  | StateInit: ssm_state
  | StateVal: v:data_value -> ssm_state
  | StateFail: ssm_state

let apply_state_op (o: state_op) (s: ssm_state) = 
  match s with
  | StateFail -> StateFail
  | StateInit -> (match o with 
                  | Get _ v ->  if v = Null then StateVal v
                                else StateFail
                  | Put _ v -> StateVal v
                 )
  | StateVal v -> (match o with
                  | Get _ v' -> if v = v' then s
                                else StateFail
                  | Put _ v' -> StateVal v'
                  )

let ssm_k = SeqMachine StateInit StateFail apply_state_op

(* state seq machine *)
let ssm = PSM ssm_k key_of

let has_some_put_k (s: seq state_op) =
  exists_sat_elems Put? s

let last_put_idx_k (s: seq state_op{has_some_put_k s}) =
  last_index Put? s

let last_put_value_or_null_k (s: seq state_op) =
  if has_some_put_k s then Put?.v (index s (last_put_idx_k s))
  else Null

val lemma_first_invalid_implies_invalid_get (s: seq state_op{length s > 0}):
  Lemma (requires (not (valid ssm_k s) /\ valid ssm_k (prefix s (length s - 1))))
        (ensures (Get? (index s (length s - 1)) /\
                  Get?.v (index s (length s - 1)) <> 
                  last_put_value_or_null_k (prefix s (length s - 1)))) 

(* validity under state seq machine is equivalent to rw_consistency *)
val lemma_state_sm_equiv_rw_consistent (s: seq state_op):
  Lemma (valid_all ssm s <==> rw_consistent s)
