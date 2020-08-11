module Veritas.StateSeqMachine

open FStar.Seq
open Veritas.Record
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

(* validity under state seq machine is equivalent to rw_consistency *)
val lemma_state_sm_equiv_rw_consistent (s: seq state_op):
  Lemma (valid_all ssm s <==> rw_consistent s)
