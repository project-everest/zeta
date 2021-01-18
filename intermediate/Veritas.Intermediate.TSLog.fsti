module Veritas.Intermediate.TSLog

open Veritas.Interleave
open Veritas.State
open Veritas.Intermediate.Global
open Veritas.Intermediate.Logs

module IntL = Veritas.Intermediate.Logs

let il_logS vcfg = interleaving (logS_entry vcfg)

let thread_count #vcfg (il:il_logS vcfg) = Seq.length (s_seq il)

let valid_tid #vcfg (il:il_logS vcfg) = tid:nat{tid < thread_count il}

let g_logS_of #vcfg (il:il_logS vcfg): g_logS _ = s_seq il

let to_state_ops #vcfg (itsl:il_logS vcfg): Seq.seq (state_op) =
  IntL.to_state_ops (i_seq itsl)
