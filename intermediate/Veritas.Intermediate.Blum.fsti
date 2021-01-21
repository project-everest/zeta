module Veritas.Intermediate.Blum

open FStar.Seq
open Veritas.Key
open Veritas.MultiSet
open Veritas.MultiSetHash
open Veritas.Intermediate.Global
open Veritas.Intermediate.Logs
open Veritas.Intermediate.TSLog
open Veritas.Intermediate.Thread
open Veritas.Intermediate.VerifierConfig

module I = Veritas.Interleave
module SpecB = Veritas.Verifier.Blum
module IntG = Veritas.Intermediate.Global
module IntT = Veritas.Intermediate.Thread

(* sequence of blum adds in the time sequenced log *)
val add_seq (#vcfg:_) (ils: its_log vcfg): seq ms_hashfn_dom

(* the addset in a time sequenced log *)
let add_set #vcfg (ils: its_log vcfg): mset_ms_hashfn_dom 
  = seq2mset #_ #ms_hashfn_dom_cmp (add_seq ils)

let blum_add_elem (#vcfg:_) (itsl: its_log vcfg) (i: I.seq_index itsl {is_blum_add (I.index itsl i)}) = 
  IntT.blum_add_elem (I.index itsl i)
  
val lemma_add_elem_correct (#vcfg:_) (itsl: its_log vcfg) (i: I.seq_index itsl):
  Lemma (requires (is_blum_add (I.index itsl i)))
        (ensures (add_set itsl `contains` blum_add_elem itsl i))
        [SMTPat (I.index itsl i)]

(* sequence of blum adds restricted to key k *)
val add_seq_key (#vcfg:_) (itsl: its_log vcfg) (k:key): seq ms_hashfn_dom

(* the addset restricted to key k *)
let add_set_key (#vcfg:_) (itsl: its_log vcfg) (k:key): mset_ms_hashfn_dom
  = seq2mset #_ #ms_hashfn_dom_cmp (add_seq_key itsl k)

(* the blum adds in the time sequenced log should be the same as global add set *)
val lemma_add_set_correct (#vcfg:_) (itsl: its_log vcfg): 
  Lemma (ensures (add_set itsl == IntG.add_set (g_logS_of itsl)))

(* if the tail element is a blum add, then the add set is obtained by adding that 
 * blum add to the prefix *)
val lemma_add_set_key_extend  (#vcfg:_) (itsl: its_log vcfg {I.length itsl > 0}):
  Lemma (requires (is_blum_add (I.telem itsl)))
        (ensures (let i = I.length itsl - 1 in
                  let e = I.index itsl i in
                  let be = blum_add_elem itsl i in
                  let k = key_of be in
                  let itsl' = I.prefix itsl i in
                  add_set_key itsl k == 
                  add_elem (add_set_key itsl' k) be))

val some_add_elem_idx (#vcfg:_) (itsl: its_log vcfg) 
  (be: ms_hashfn_dom{add_set itsl `contains` be}): 
  (i:(I.seq_index itsl){is_blum_add (I.index itsl i) /\
                        be = blum_add_elem itsl i})

val lemma_add_set_key_contains_only (#vcfg:_) (itsl: its_log vcfg) (k:key) (be: ms_hashfn_dom):
  Lemma (requires (add_set_key itsl k `contains` be))
        (ensures (key_of be = k))

(* get the blum evict element from an index *)
val blum_evict_elem (#vcfg:_) (itsl: its_log vcfg) (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i)}):
  ms_hashfn_dom

(* sequence of evicts in time sequence log *)
val evict_seq (#vcfg:_) (itsl: its_log vcfg): seq ms_hashfn_dom

(* set of evicts in time sequence log *)
let evict_set #vcfg (itsl: its_log vcfg): mset_ms_hashfn_dom = 
  seq2mset #_ #ms_hashfn_dom_cmp (evict_seq itsl)

(* the evict sequence restricted to key k *)
val evict_seq_key (#vcfg:_) (itsl: its_log vcfg) (k:key): seq ms_hashfn_dom

let evict_set_key #vcfg (itsl: its_log vcfg) (k:key): mset_ms_hashfn_dom= 
  seq2mset #_ #ms_hashfn_dom_cmp (evict_seq_key itsl k)

(* the blum evicts in time sequenced log should be the same as global evict set *)
val evict_set_correct (#vcfg:_) (itsl: its_log vcfg):
  Lemma (evict_set itsl == IntG.evict_set (g_logS_of itsl))


val lemma_spec_rel_implies_same_add_seq (#vcfg:_) (ils: its_log vcfg{spec_rel ils})
  : Lemma (ensures (let ilk = to_logk ils in 
                    add_seq ils = SpecB.ts_add_seq ilk))
          [SMTPat (spec_rel ils)]
