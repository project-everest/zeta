module Zeta.InterleaveMultiSet

open FStar.Seq
open Zeta.SeqAux
open Zeta.MultiSet
open Zeta.Interleave

module I = Zeta.Interleave

(* given a sequence of sequences, a filter over indexes, and a map over indexes, define
 * a multiset *)
val sseq_indexed_filter_map_multiset
  (#a #b:_)
  (l: cmp b)                      (* linear ordering over b *)
  (s: sseq a)
  (f: sseq_index s -> bool)
  (m: (i:sseq_index s{f i} ) -> b)
  : mset b l

(* an element of the multiset can be mapped back to the index of seq of sequences *)
val sseq_some_index_of_ifp_multiset
  (#a #b:_)
  (l: cmp b)
  (s: sseq a)
  (f: sseq_index s -> bool)
  (m: (i: sseq_index s{f i}) -> b)
  (x: b{let ms = sseq_indexed_filter_map_multiset l s f m in contains ms x})
  : (i: sseq_index s {f i /\ m i = x})

(* an element of the multiset with membership 2 can be mapped back to two indexes of seq of sequences *)
val sseq_two_indexes_of_ifp_multiset
  (#a #b:_)
  (l: cmp b)
  (s: sseq a)
  (f: sseq_index s -> bool)
  (m: (i: sseq_index s{f i}) -> b)
  (x: b{let ms = sseq_indexed_filter_map_multiset l s f m in mem x ms >= 2})
  : (ij : ((sseq_index s) * (sseq_index s)) { let i,j = ij in f i /\ f j /\ m i = x /\ m j = x /\ i <> j  })

(* given an interleaved sequence, a filter over indexes, and a map over indexes, define a multiset *)
val interleave_indexed_filter_map_multiset
  (#a #b:_)
  (l: cmp b)
  (il: interleaving a)
  (f: I.seq_index il -> bool)
  (m: (i: I.seq_index il { f i }) -> b)
  : mset b l

(* an element of the multiset can be mapped back to the index of seq of sequences *)
val interleave_some_index_of_ifp_multiset
  (#a #b:_)
  (l: cmp b)
  (il: interleaving a)
  (f: I.seq_index il -> bool)
  (m: (i: I.seq_index il{f i}) -> b)
  (x: b{let ms = interleave_indexed_filter_map_multiset l il f m in contains ms x})
  : (i: I.seq_index il {f i /\ m i = x})

(* an element of the multiset with membership 2 can be mapped back to two indexes of seq of sequences *)
val interleave_two_indexes_of_ifp_multiset
  (#a #b:_)
  (l: cmp b)
  (il: interleaving a)
  (f: I.seq_index il -> bool)
  (m: (i: I.seq_index il{f i}) -> b)
  (x: b{let ms = interleave_indexed_filter_map_multiset l il f m in mem x ms >= 2})
  : (ij : ((I.seq_index il) * (I.seq_index il)) { let i,j = ij in f i /\ f j /\ m i = x /\ m j = x /\ i <> j  })
