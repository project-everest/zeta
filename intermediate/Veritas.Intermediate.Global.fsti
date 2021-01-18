module Veritas.Intermediate.Global

open FStar.Seq
open Veritas.MultiSetHashDomain
open Veritas.SeqAux
open Veritas.Intermediate.Logs
open Veritas.Intermediate.Thread

module SA = Veritas.SeqAux
module IntLog = Veritas.Intermediate.Logs
module IntT = Veritas.Intermediate.Thread

let g_logS vcfg = seq (logS vcfg)

let thread_log #vcfg (gl:g_logS vcfg) (tid:seq_index gl): thread_id_logS _ = 
   (tid, Seq.index gl tid)

let to_state_ops #vcfg (gl:g_logS vcfg) =
  map IntLog.to_state_ops gl

let verifiable #vcfg (gl: g_logS vcfg) = 
  forall (tid:seq_index gl). {:pattern IntT.verify (thread_log gl tid)} IntT.verifiable (thread_log gl tid)

let verifiable_log vcfg = gl:g_logS vcfg{verifiable gl}

val verifiable_implies_prefix_verifiable
  (#vcfg:_) (gl:verifiable_log vcfg) (i:nat{i <= Seq.length gl}):
  Lemma (ensures (verifiable #vcfg (SA.prefix gl i)))
        [SMTPat (SA.prefix gl i)]

val hadd (#vcfg:_) (gl: verifiable_log vcfg): ms_hash_value
val hevict (#vcfg:_) (gl: verifiable_log vcfg): ms_hash_value

let hash_verifiable #vcfg (gl: verifiable_log vcfg): bool = 
  hadd gl = hevict gl

let hash_verifiable_log vcfg = gl:verifiable_log vcfg{hash_verifiable gl}
