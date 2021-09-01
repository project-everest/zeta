module Zeta.Interleave

open FStar.Seq
open Zeta.SeqAux
open Zeta.SSeq
open Zeta.FilterMap

module S = FStar.Seq
module SA = Zeta.SeqAux

(* an interleaving of n sequences specifed by storing the mapping from every
 * interleaved element to the id of the originating sequence *)
type interleaving (a:eqtype) = {
  n:nat;
  st:seq (a & t:nat{t < n});
}

val i_seq (#a:_) (il: interleaving a): (s: seq a {S.length il.st = S.length s})

val s_seq (#a:_) (il: interleaving a): ss:sseq a{S.length ss = il.n}

let length (#a:eqtype) (il: interleaving a)
  = length il.st

let seq_index (#a:eqtype) (il: interleaving a) = i:nat{i < length il}

let index (#a: eqtype) (il: interleaving a) (i: seq_index il)
  = S.index (i_seq il) i

let prefix_of (#a:eqtype) (s0 s1:seq a) = is_prefix s1 s0

let sseq_all_prefix_of (#a:eqtype) 
                       (ss0 ss1: sseq a)
  = S.length ss0 = S.length ss1 /\
    (forall (tid:SA.seq_index ss1). (Seq.index ss0 tid) `prefix_of` (Seq.index ss1 tid))

val prefix (#a:_) (il: interleaving a) (i:nat{i <= length il})
  : (il':interleaving a {i_seq il' = SA.prefix (i_seq il) i})

val per_thread_prefix (#a:eqtype) (il: interleaving a) (i:nat{i <= length il})
  : Lemma (let ss = s_seq il in
           let il' = prefix il i in
           let ss' = s_seq il' in
           ss' `sseq_all_prefix_of` ss)

val i2s_map (#a:_) (il:interleaving a) (i:seq_index il)
  : (si:sseq_index (s_seq il){index il i = indexss (s_seq il) si})

val s2i_map (#a:eqtype) (il:interleaving a) (si: sseq_index (s_seq il)):
  (i:seq_index il{index il i = indexss (s_seq il) si /\
                  i2s_map il i = si})

val lemma_i2s_s2i (#a:eqtype) (il:interleaving a) (i:seq_index il):
  Lemma (ensures (s2i_map il (i2s_map il i) = i))
        [SMTPat (i2s_map il i)]

let hprefix (#a:_) (il:interleaving a {length il > 0})
  = prefix il (length il - 1)

let telem (#a:_) (il:interleaving a {length il > 0})
  = SA.telem (i_seq il)

val prefix_identity (#a:eqtype) (il:interleaving a)
  : Lemma (ensures prefix il (length il) == il)

val lemma_prefix_index (#a:eqtype) (il:interleaving a) (i:nat{i <= length il}) (j:nat{j < i}):
  Lemma (ensures (index (prefix il i) j = index il j))
        [SMTPat (index (prefix il i) j)]

val lemma_prefix_prefix (#a:eqtype) (il:interleaving a) (i:nat{i <= length il}) (j:nat{j <= i}):
  Lemma (ensures (prefix (prefix il i) j == prefix il j))
        [SMTPat (prefix (prefix il i) j)]

val some_interleaving (#a: eqtype) (ss: sseq a)
  : il: interleaving a {s_seq il = ss}

let interleave (#a:eqtype) (s: seq a) (ss: sseq a)
  = exists il. (i_seq il = s) /\ (s_seq il = ss)
