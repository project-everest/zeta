module Veritas.SeqMachine

open FStar.Seq
open Veritas.SeqAux

(* a transition function tr is failure propagating
 * if it remains in failure state once entered
 *)
let failure_prop_fn (#a:eqtype) (#st:eqtype) (sf:st) (tr:a -> st -> st) 
  = forall (a1:a). tr a1 sf = sf

noeq type seq_machine = 
  | SeqMachine: #a:eqtype ->                                  // elements of sequence
                #st:eqtype ->                               // state type
                s0:st ->                                    // initial state
                sf:st{sf <> s0} ->                           // final state
                tr: (a -> st -> st){failure_prop_fn sf tr}  // transition function
                -> seq_machine

let elem_type (sm: seq_machine) = 
  match sm with
  | SeqMachine #a #_ _ _ _ -> a

let state_type (sm: seq_machine) = 
  match sm with 
  | SeqMachine #_ #s _ _ _ -> s

let init_state (sm: seq_machine): Tot (state_type sm) = 
  match sm with 
  | SeqMachine s0 _ _ -> s0

let fail_state (sm: seq_machine): Tot (state_type sm) = 
  match sm with
  | SeqMachine _ sf _ -> sf

let trans_fn (sm: seq_machine): 
  Tot (tr: ((elem_type sm) -> (state_type sm) -> (state_type sm))
           {failure_prop_fn (fail_state sm) tr}) = 
  match sm with
  | SeqMachine _ _ tr -> tr

(* run the seq machine on a sequence *)
let seq_machine_run (sm: seq_machine) (s: seq (elem_type sm)): Tot (state_type sm) = 
  reduce (init_state sm) (trans_fn sm) s

(* validity: we donot end up with the failure state *)
let valid (sm: seq_machine) (s: seq (elem_type sm)) = 
  (fail_state sm) <> (seq_machine_run sm s)

(* empty sequence is valid *)
val lemma_empty_seq_valid (sm: seq_machine):
  Lemma (valid sm (empty #(elem_type sm)))

val lemma_valid_prefix (sm: seq_machine) (s: (seq (elem_type sm)){valid sm s}) (i:nat{i <= length s}):
  Lemma (valid sm (prefix s i))

(* the maximum valid prefix of a sequence is computable *)
val max_valid_prefix (sm: seq_machine) (s: seq (elem_type sm))
  : Tot (i:nat{i <= length s /\ 
              valid sm (prefix s i) /\
              (i < length s ==> not (valid sm (prefix s (i + 1))))
              })

(* partitioned seq_machine *)
noeq type pseq_machine =
  | PSM: #key:eqtype -> sm: seq_machine -> pf: ((elem_type sm) -> key) -> pseq_machine

let seq_machine_of (psm: pseq_machine) = 
  match psm with
  | PSM sm _ -> sm

let key_type (psm: pseq_machine): eqtype = 
  match psm with
  | PSM #k _ _ -> k

let elem_type_p (psm: pseq_machine) = elem_type (seq_machine_of psm)

let partn_fn (psm: pseq_machine): (elem_type_p psm -> key_type psm)  = 
  match psm with
  | PSM _ pf -> pf

let valid_all (psm: pseq_machine) (s: seq (elem_type_p psm)) = 
  forall (k:(key_type psm)). valid (seq_machine_of psm) (filter (fun e -> (partn_fn psm e) = k) s)

val lemma_empty_seq_valid_all (psm: pseq_machine):
  Lemma (valid_all psm (empty #(elem_type_p psm)))

val lemma_valid_all_prefix (psm: pseq_machine) 
                           (s: (seq (elem_type_p psm)){valid_all psm s}) (i:nat{i <= length s}):
  Lemma (valid_all psm (prefix s i))

val max_valid_all_prefix (psm: pseq_machine) (s: seq (elem_type_p psm))
  : Tot (i: nat{i <= length s /\
               valid_all psm (prefix s i) /\
               (i < length s ==> ~ (valid_all psm (prefix s (i + 1))))})

