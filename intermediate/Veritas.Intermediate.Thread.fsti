module Veritas.Intermediate.Thread

open Veritas.BinTree
open Veritas.MultiSetHashDomain
open Veritas.Record
open Veritas.SeqAux
open Veritas.Intermediate.Logs
open Veritas.Intermediate.Store
open Veritas.Intermediate.Verify
open Veritas.Intermediate.VerifierConfig

module SA = Veritas.SeqAux
module IntV = Veritas.Intermediate.Verify

let thread_id_logS vcfg = thread_id & logS vcfg

let thread_id_of #vcfg (tl: thread_id_logS vcfg): nat = fst tl

let logS_of #vcfg (tl: thread_id_logS vcfg): logS _ = snd tl

let length #vcfg (tl: thread_id_logS vcfg): nat =
  Seq.length (logS_of tl)

let tl_idx #vcfg (tl: thread_id_logS vcfg) = i:nat{i < length tl}

let index #vcfg (tl: thread_id_logS vcfg) (i:tl_idx tl): logS_entry _ =
  Seq.index (logS_of tl) i

let prefix #vcfg (tl: thread_id_logS vcfg) (i:nat{i <= length tl}): thread_id_logS _ =
  (thread_id_of tl), (SA.prefix (logS_of tl) i)

let init_store vcfg (tid:thread_id): vstore _ = 
  let st = empty_store vcfg in
  if tid = 0 then 
    madd_to_store_root st 0 (init_value Root) 
  else
    st

val lemma_init_store_ismap (vcfg:verifier_config) (tid:thread_id)
  : Lemma (ensures (is_map (init_store vcfg tid)))
          [SMTPat (init_store vcfg tid)]

val lemma_init_store_slot_points_to_is_merkle_points_to (vcfg:verifier_config) (tid:thread_id)
  : Lemma (ensures (slot_points_to_is_merkle_points_to (init_store vcfg tid)))
          [SMTPat (init_store vcfg tid)]

let verify #vcfg (tl:thread_id_logS vcfg): vtls _ =
  let (tid,l) = tl in
  let st = init_store vcfg tid in
  let vs = IntV.init_thread_state tid st in
  IntV.verify vs l

let verifiable #vcfg (tl:thread_id_logS vcfg) = 
  IntV.Valid? (verify tl)

let verifiable_log vcfg = tl:thread_id_logS vcfg{verifiable tl}

val verifiable_implies_prefix_verifiable
  (#vcfg:_) (tl:verifiable_log vcfg) (i:nat{i <= length tl}):
  Lemma (ensures (verifiable (prefix tl i)))
        [SMTPat (prefix tl i)]

(* clock after processing the i'th entry *)
let clock #vcfg (tl:verifiable_log vcfg) (i:tl_idx tl): timestamp =
  let vs = verify (prefix tl (i + 1)) in
  Valid?.clock (verify (prefix tl (i + 1)))
