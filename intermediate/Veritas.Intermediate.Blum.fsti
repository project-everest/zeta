module Veritas.Intermediate.Blum

open FStar.Seq
open Veritas.Key
open Veritas.MultiSet
open Veritas.MultiSetHash
open Veritas.Intermediate.Global
open Veritas.Intermediate.Logs
open Veritas.Intermediate.Store
open Veritas.Intermediate.TSLog
open Veritas.Intermediate.Thread
open Veritas.Intermediate.Verify
open Veritas.Intermediate.VerifierConfig

module I = Veritas.Interleave
module MS = Veritas.MultiSet
module SpecV = Veritas.Verifier
module SpecB = Veritas.Verifier.Blum
module SpecT = Veritas.Verifier.Thread
module SpecTS = Veritas.Verifier.TSLog
module IntV = Veritas.Intermediate.Verify
module IntG = Veritas.Intermediate.Global
module IntT = Veritas.Intermediate.Thread
module IntTS = Veritas.Intermediate.TSLog

(* sequence of blum adds in the time sequenced log *)
val add_seq (#vcfg:_) (ep: epoch) (ils: its_log vcfg): seq ms_hashfn_dom

(* the addset in a time sequenced log *)
let add_set #vcfg (ep: epoch) (ils: its_log vcfg): mset_ms_hashfn_dom
  = seq2mset #_ #ms_hashfn_dom_cmp (add_seq ep ils)

let blum_add_elem (#vcfg:_) (itsl: its_log vcfg) (i: I.seq_index itsl {is_blum_add (I.index itsl i)}) = 
  IntT.blum_add_elem (I.index itsl i)

val lemma_add_elem_correct (#vcfg:_) (itsl: its_log vcfg) (i: I.seq_index itsl):
  Lemma (requires (is_blum_add (I.index itsl i)))
        (ensures (let be = blum_add_elem itsl i in
                  let ep = epoch_of be in
                  add_set ep itsl `MS.contains` be))
        [SMTPat (I.index itsl i)]

(* the blum adds in the time sequenced log should be the same as global add set *)
val lemma_add_set_correct (#vcfg:_) (ep: epoch) (itsl: its_log vcfg):
  Lemma (ensures (add_set ep itsl == IntG.add_set ep (g_logS_of itsl)))

val lemma_add_set_extend  (#vcfg:_) (itsl: its_log vcfg {I.length itsl > 0}):
  Lemma (requires (is_blum_add (I.telem itsl)))
        (ensures (let i = I.length itsl - 1 in
                  let e = I.index itsl i in
                  let be = blum_add_elem itsl i in
                  let ep = epoch_of be in
                  let itsl' = I.prefix itsl i in
                  add_set ep itsl ==
                  add_elem (add_set ep itsl') be))

(* get the blum evict element from an index *)
let blum_evict_elem (#vcfg:_) (itsl: its_log vcfg) (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i)}): ms_hashfn_dom  =
  IntTS.blum_evict_elem itsl i

val lemma_blum_evict_elem (#vcfg:_) (ils: its_log vcfg) (i:nat{i <= I.length ils}) (j:nat{j < i})
  : Lemma (requires (is_evict_to_blum (I.index ils j)))
          (ensures (blum_evict_elem ils j = blum_evict_elem (I.prefix ils i) j))

(* sequence of evicts in time sequence log *)
val evict_seq (#vcfg:_) (ep: epoch) (itsl: its_log vcfg): seq ms_hashfn_dom

(* set of evicts in time sequence log *)
let evict_set #vcfg (ep: epoch) (itsl: its_log vcfg): mset_ms_hashfn_dom =
  seq2mset #_ #ms_hashfn_dom_cmp (evict_seq ep itsl)

(* the blum evicts in time sequenced log should be the same as global evict set *)
val evict_set_correct (#vcfg:_) (ep: epoch) (itsl: its_log vcfg):
  Lemma (ensures (evict_set ep itsl == IntG.evict_set ep (g_logS_of itsl)))

val lemma_evict_elem_correct (#vcfg:_) (itsl: its_log vcfg) (i: I.seq_index itsl):
  Lemma (requires (is_evict_to_blum (I.index itsl i)))
        (ensures (let be = blum_evict_elem itsl i in
                  let ep = epoch_of be in
                  evict_set ep itsl `MS.contains` be))

val lemma_evict_set_extend2 (#vcfg:_) (itsl: its_log vcfg{I.length itsl > 0}):
  Lemma (requires (let i = I.length itsl - 1 in  
                   not (is_evict_to_blum (I.index itsl i))))
        (ensures (let i = I.length itsl - 1 in  
                  evict_set itsl == evict_set (I.prefix itsl i)))

val lemma_spec_rel_implies_same_add_elem (#vcfg:_) 
                                         (ils: its_log vcfg{spec_rel ils}) 
                                         (i: I.seq_index ils{is_blum_add (I.index ils i)}):
  Lemma (ensures (let ilk = IntTS.to_logk ils in
                  SpecV.is_blum_add (I.index ilk i) /\
                  SpecT.blum_add_elem (I.index ilk i) = blum_add_elem ils i))
 
val lemma_spec_rel_implies_same_add_seq (#vcfg:_) (ils: its_log vcfg{spec_rel ils})
  : Lemma (ensures (let ilk = to_logk ils in 
                    add_seq ils = SpecB.ts_add_seq ilk))
          [SMTPat (spec_rel ils)]

val lemma_spec_rel_implies_same_evict_elem (#vcfg:_) 
                                         (ils: its_log vcfg{spec_rel ils}) 
                                         (i: I.seq_index ils{is_evict_to_blum (I.index ils i)}):
  Lemma (ensures (let ilk = IntTS.to_logk ils in
                  SpecV.is_evict_to_blum (I.index ilk i) /\
                  SpecB.blum_evict_elem ilk i = blum_evict_elem ils i))

val lemma_spec_rel_implies_same_evict_seq (#vcfg:_) (ils: its_log vcfg{spec_rel ils})
  : Lemma (ensures (let ilk = to_logk ils in 
                    evict_seq ils = SpecB.ts_evict_seq ilk))
          [SMTPat (spec_rel ils)]

(* since evict_set is a pure set (not a multiset) we can identify the unique index 
 * for each element of the set *)
val index_blum_evict (#vcfg:_) (itsl: its_log vcfg) (e: ms_hashfn_dom {evict_set itsl `contains` e}):
  (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i) /\ 
                      blum_evict_elem itsl i = e})

(* if the blum add occurs in the blum evict set, its index is earlier *)
val lemma_evict_before_add (#vcfg:_) (itsl: its_log vcfg) (i:I.seq_index itsl{is_blum_add (I.index itsl i)}):
  Lemma (ensures (not (evict_set itsl `contains` blum_add_elem itsl i)) \/
                  index_blum_evict itsl (blum_add_elem itsl i) < i)

/// index of some add element given that the the add set contains the element
/// 
val some_add_elem_idx (#vcfg:_) (itsl: its_log vcfg) 
                                (be: ms_hashfn_dom{add_set itsl `contains` be}):
   (i:(I.seq_index itsl){is_blum_add (I.index itsl i) /\ be = blum_add_elem itsl i})

/// The membership of an element in a prefix addset <= membership in the full addset 
val lemma_mem_monotonic_add_set (#vcfg:_) (be:ms_hashfn_dom) (itsl: its_log vcfg) (i:nat{i <= I.length itsl}):
  Lemma (mem be (add_set itsl) >= mem be (add_set (I.prefix itsl i)))

///  for any prefix of itsl, there exists an element be whose membership in add set > membership in evict set, then
///  the add and evict sets of the entire sequence cannot be equal.
///  The intuition is that a matching element of be in an evict set happens prior to that of add set meaning there 
///  cannot be element be in the suffix. This implies the add- and evict-sets cannot be equal.
val lemma_add_delta_implies_not_eq (#vcfg:_) (itsl: its_log vcfg) (i:nat{i <= I.length itsl}) (be:ms_hashfn_dom):
    Lemma (requires (let itsli = I.prefix itsl i in
                     MS.mem be (add_set itsli) > MS.mem be (evict_set itsli)))
          (ensures (~ ((add_set itsl) == (evict_set itsl))))
