module Zeta.InterleaveMultiSet

open FStar.Seq
open Zeta.SeqAux
open Zeta.MultiSet
open Zeta.Interleave

module I = Zeta.Interleave
module SA = Zeta.SeqAux

(* given a sequence, define a multiset of elements produced by mapping positions i of the
 * sequence to elements of a domain b, using a mapping function m. The positions could satisfy a filter f
 * and the mapping could be defined only over such positions. *)
val seq_indexed_filter_map_multiset
  (#a #b:_)
  (l: cmp b)
  (s: seq a)
  (f: SA.seq_index s -> bool)
  (m: (i: SA.seq_index s {f i}) -> b)
  : mset b l

(* for each element of a multiset we can identify an index in the original sequence corresponding to it*)
val seq_some_index_of_ifp
  (#a #b:_)
  (l: cmp b)
  (s: seq a)
  (f: SA.seq_index s -> bool)
  (m: (i: SA.seq_index s {f i}) -> b)
  (x: b{let ms = seq_indexed_filter_map_multiset l s f m in contains ms x})
  : (i: SA.seq_index s{f i /\ m i = x})

(* for an element with membership count >= 2, we can identify two indices *)
val seq_two_indexes_of_ifp
  (#a #b:_)
  (l: cmp b)
  (s: seq a)
  (f: SA.seq_index s -> bool)
  (m: (i: SA.seq_index s {f i}) -> b)
  (x: b{let ms = seq_indexed_filter_map_multiset l s f m in mem x ms >= 2})
  : (ij: (SA.seq_index s * SA.seq_index s){
        let i,j = ij in
        f i /\ m i = x /\
        f j /\ m j = x /\
        i <> j})

(* given a sequence of sequences, a filter over indexes, and a map over indexes, define
 * a multiset *)
val sseq_indexed_filter_map_multiset
  (#a #b:_)
  (l: cmp b)
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
let interleave_indexed_filter_map_multiset
  (#a #b:_)
  (l: cmp b)
  (il: interleaving a)
  (f: I.seq_index il -> bool)
  (m: (i: I.seq_index il { f i }) -> b)
  : mset b l
  = seq_indexed_filter_map_multiset l (I.i_seq il) f m

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

val lemma_interleave_ifp_correct1
  (#a #b:_)
  (l: cmp b)
  (il: interleaving a)
  (f: I.seq_index il -> bool)
  (m: (i: I.seq_index il{f i}) -> b)
  : Lemma (ensures (
    let ss = s_seq il in
    let f' = fun (ii: sseq_index ss) ->
      let j' = s2i_map il ii in
      f j' in
    let m' = fun (ii: sseq_index ss {f' ii}) ->
      let j' = s2i_map il ii in
      m j' in
    sseq_indexed_filter_map_multiset l ss f' m' ==
    interleave_indexed_filter_map_multiset l il f m))
    [SMTPat (interleave_indexed_filter_map_multiset l il f m)]

val lemma_interleave_ifp_correct2
  (#a #b:_)
  (l: cmp b)
  (il: interleaving a)
  (f: sseq_index (s_seq il) -> bool)
  (m: (i: sseq_index (s_seq il){f i}) -> b)
  : Lemma (ensures (
    let ss = s_seq il in
    let f' = fun (i: I.seq_index il) ->
      let jj = i2s_map il i in
      f jj in
    let m' = fun (i: I.seq_index il {f' i}) ->
      let jj = i2s_map il i in
      m jj in
    sseq_indexed_filter_map_multiset l ss f m ==
    interleave_indexed_filter_map_multiset l il f' m'))
