module Veritas.Intermediate.Logs

open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSetHashDomain
open Veritas.Record
open Veritas.SeqAux
open Veritas.State
open Veritas.Intermediate.VerifierConfig

module Spec = Veritas.Verifier

(* Definitions of different styles of verifier logs.
   - logK : contains only key references (defined in Veritas.Verifier)
   - logS: contains slot references
   - logL: contains slot references & low-level data structures (TODO) *)

let thread_id = Spec.thread_id

let logK_entry = Spec.vlog_entry
let logK = Spec.vlog

type logS_entry (vcfg:verifier_config) =
  | Get_S: s:slot_id vcfg -> k:data_key -> v:data_value -> logS_entry vcfg
  | Put_S: s:slot_id vcfg -> k:data_key -> v:data_value -> logS_entry vcfg
  | AddM_S: s:slot_id vcfg -> r:record -> s':slot_id vcfg -> logS_entry vcfg
  | EvictM_S: s:slot_id vcfg -> s':slot_id vcfg -> logS_entry vcfg
  | AddB_S: s:slot_id vcfg -> r:record -> t:timestamp -> j:thread_id -> logS_entry vcfg
  | EvictB_S: s:slot_id vcfg -> t:timestamp -> logS_entry vcfg
  | EvictBM_S: s:slot_id vcfg -> s':slot_id vcfg -> t:timestamp -> logS_entry vcfg
             
let logS vcfg = Seq.seq (logS_entry vcfg)

let is_state_op #vcfg (e: logS_entry vcfg): bool =
  match e with
  | Get_S _ _ _ | Put_S _ _ _ -> true
  | _ -> false

let to_state_op #vcfg (e:logS_entry vcfg {is_state_op e}): state_op =
  match e with
  | Get_S _ k v -> Get k v
  | Put_S _ k v -> Put k v

let to_state_op_logS #vcfg (l: logS vcfg) =
  map to_state_op (filter_refine is_state_op l)

(* Reproducing definitions from Veritas.Verifier.Thread *)

let thread_id_logS (vcfg:verifier_config) = thread_id & logS vcfg

let thread_id_of #vcfg (tl: thread_id_logS vcfg): nat = fst tl

let logS_of #vcfg (tl: thread_id_logS vcfg): logS _ = snd tl

let tl_length #vcfg (tl: thread_id_logS vcfg): nat =
  Seq.length (logS_of tl)

let tl_idx #vcfg (tl: thread_id_logS vcfg) = i:nat{i < tl_length tl}

let tl_index #vcfg (tl: thread_id_logS vcfg) (i:tl_idx tl): logS_entry _ =
  Seq.index (logS_of tl) i

let tl_prefix #vcfg (tl: thread_id_logS vcfg) (i:nat{i <= tl_length tl}): thread_id_logS _ =
  (thread_id_of tl), (prefix (logS_of tl) i)

(* Reproducing definitions from Veritas.Verifier.Global *)

let g_logS vcfg = Seq.seq (logS vcfg)

let thread_log #vcfg (gl:g_logS vcfg) (tid:seq_index gl): thread_id_logS _ = 
   (tid, Seq.index gl tid)

let to_state_op_glogS #vcfg (gl:g_logS vcfg) =
  map to_state_op_logS gl

(* Reproducing definitions from Veritas.Verifier.TSLog *)

let il_logS vcfg = interleaving (logS_entry vcfg)

let thread_count #vcfg (il:il_logS vcfg) = Seq.length (s_seq il)

let valid_tid #vcfg (il:il_logS vcfg) = tid:nat{tid < thread_count il}

let g_logS_of #vcfg (il:il_logS vcfg): g_logS _ = s_seq il

let state_ops #vcfg (itsl:il_logS vcfg): Seq.seq (state_op) =
  to_state_op_logS (i_seq itsl)

let lemma_logS_interleave_implies_state_ops_interleave #vcfg (l: logS vcfg) (gl: g_logS vcfg{interleave #(logS_entry vcfg) l gl})
  : Lemma (interleave #state_op (to_state_op_logS l) (to_state_op_glogS gl)) 
  = FStar.Squash.bind_squash
      #(interleave l gl)
      #(interleave (to_state_op_logS l) (to_state_op_glogS gl))
      ()
      (fun i -> 
        let i' = filter_map_interleaving is_state_op to_state_op i in
        FStar.Squash.return_squash i')
