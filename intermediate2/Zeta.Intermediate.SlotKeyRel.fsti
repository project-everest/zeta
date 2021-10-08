module Zeta.Intermediate.SlotKeyRel

open Zeta.Key
open Zeta.Intermediate.VerifierConfig

(**
 * The definitions in this file capture the relationship between slots and keys.
 * A slot is a smaller domain of values that are temporarily associated with keys.
 *)

type slot_state = 
  | Free: slot_state 
  | Assoc: k:base_key -> slot_state

(* mapping from a slot to its state *)
let slot_state_map vcfg = slot_id vcfg -> slot_state 

let is_free (#vcfg:_) (ssm:slot_state_map vcfg) (s: slot_id vcfg): bool = 
  ssm s = Free

let is_assoc (#vcfg:_) (ssm:slot_state_map vcfg) (s:slot_id vcfg): bool =
  not (is_free ssm s)

let assoc_key (#vcfg:_) (ssm:slot_state_map vcfg) (s:slot_id vcfg{is_assoc ssm s}): base_key =
  Assoc?.k (ssm s)

let is_assoc_with #vcfg (ssm:slot_state_map vcfg) (s:slot_id vcfg) (k:base_key): bool =
  is_assoc ssm s && assoc_key ssm s = k
