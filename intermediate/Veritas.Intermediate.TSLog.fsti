module Veritas.Intermediate.TSLog

open Veritas.Interleave
open Veritas.State
open Veritas.Intermediate.Global
open Veritas.Intermediate.Logs

module I = Veritas.Interleave
module IntL = Veritas.Intermediate.Logs
module IntG = Veritas.Intermediate.Global

let il_logS vcfg = interleaving (logS_entry vcfg)

let thread_count #vcfg (il:il_logS vcfg) = Seq.length (s_seq il)

let valid_tid #vcfg (il:il_logS vcfg) = tid:nat{tid < thread_count il}

let g_logS_of #vcfg (il:il_logS vcfg): g_logS _ = s_seq il

let to_state_ops #vcfg (itsl:il_logS vcfg): Seq.seq (state_op) =
  IntL.to_state_ops (i_seq itsl)

let verifiable #vcfg (il: il_logS vcfg) = 
  IntG.verifiable (g_logS_of il)

val clock_sorted (#vcfg:_) (il: il_logS vcfg {verifiable il}): prop

let its_log vcfg = il:il_logS vcfg{verifiable il /\ clock_sorted il}

val create (#vcfg:_) (gl: verifiable_log vcfg): (itsl:its_log vcfg{g_logS_of itsl == gl})

let hash_verifiable #vcfg (itsl: its_log vcfg) = IntG.hash_verifiable (g_logS_of itsl)

let hash_verifiable_log vcfg = itsl: its_log vcfg{hash_verifiable itsl}

val lemma_prefix_verifiable (#vcfg:_) (itsl: its_log vcfg) (i:nat{i <= I.length itsl}):
  Lemma (ensures (verifiable (I.prefix itsl i) /\ clock_sorted (I.prefix itsl i)))
        [SMTPat (I.prefix itsl i)]

let lemma_logS_interleave_implies_state_ops_interleave #vcfg (l: logS vcfg) (gl: g_logS vcfg{interleave #(logS_entry vcfg) l gl})
  : Lemma (interleave #state_op (IntL.to_state_ops l) (IntG.to_state_ops gl)) 
  = FStar.Squash.bind_squash
      #(interleave l gl)
      #(interleave (IntL.to_state_ops l) (IntG.to_state_ops gl))
      ()
      (fun i -> 
        let i' = filter_map_interleaving is_state_op to_state_op i in
        FStar.Squash.return_squash i')
