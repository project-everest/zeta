module Zeta.Interleave

open FStar.Seq
open Zeta.SeqAux
open Zeta.SSeq

module S = FStar.Seq
module SA = Zeta.SeqAux

type elem_src (a:eqtype) (n:nat) = {
  e: a;
  s: t:nat{t< n};
}

(* an interleaving of n sequences specifed by storing the mapping from every
 * interleaved element to the id of the src sequence *)
type interleaving (a:eqtype) (n:nat) = seq (elem_src a n)

let prefix (#a:_) (#n:_) (il: interleaving a n) (i:nat{i <= length il})
  : interleaving a n
  = SA.prefix il i

val i_seq (#a:_) (#n:nat) (il: interleaving a n)
  : is: seq a {length is = length il }

let src (#a:_) (#n:_) (il: interleaving a n) (i: SA.seq_index il)
  = (S.index il i).s

let index (#a:_) (#n:_) (il: interleaving a n) (i: SA.seq_index il)
  = S.index (i_seq il) i

val index_prop (#a #n:_) (il: interleaving a n) (i: SA.seq_index il)
  : Lemma (ensures ((S.index il i).e = index il i))
          [SMTPat (index il i)]

val s_seq (#a:_) (#n:_) (il: interleaving a n): ss:sseq a{S.length ss = n}

val per_thread_prefix (#a:_) (#n:_) (il: interleaving a n) (i:nat{i <= length il})
  : Lemma (let ss = s_seq il in
           let il' = prefix il i in
           let ss' = s_seq il' in
           ss' `sseq_all_prefix_of` ss)

val i2s_map (#a:_) (#n:_) (il:interleaving a n) (i: SA.seq_index il)
  : (si:sseq_index (s_seq il){index il i = indexss (s_seq il) si /\ fst si = src il i})

val i2s_map_monotonic (#a #n:_) (il: interleaving a n) (i j: SA.seq_index il)
  : Lemma (requires (src il i = src il j))
          (ensures ((i < j ==> snd (i2s_map il i) < snd (i2s_map il j)) /\
                    (j < i ==> snd (i2s_map il j) < snd (i2s_map il i))))

val s2i_map (#a:eqtype) (#n:_) (il:interleaving a n) (si: sseq_index (s_seq il)):
  (i: SA.seq_index il{index il i = indexss (s_seq il) si /\
                      i2s_map il i = si /\ src il i = fst si})

val s2i_map_monotonic (#a #n:_) (il: interleaving a n) (i j: sseq_index (s_seq il))
  : Lemma (requires (fst i = fst j))
          (ensures ((snd i < snd j ==> s2i_map il i < s2i_map il j) /\
                    (snd j < snd i ==> s2i_map il j < s2i_map il i)))

val lemma_i2s_s2i (#a:_) (#n:_) (il:interleaving a n) (i: SA.seq_index il):
  Lemma (ensures (s2i_map il (i2s_map il i) = i))
        [SMTPat (i2s_map il i)]

let hprefix (#a:_) (#n:_) (il:interleaving a n {length il > 0})
  = prefix il (length il - 1)

let telem (#a:_) (#n:_) (il:interleaving a n {length il > 0})
  = SA.telem (i_seq il)

val lemma_index_prefix_property (#a:_) (#n:_) (il:interleaving a n) (i:nat{i <= length il}) (j:nat{j < i}):
  Lemma (ensures (index (prefix il i) j = index il j))
        [SMTPat (index (prefix il i) j)]

val lemma_prefix_prefix_property (#a:_) (#n:_) (il:interleaving a n) (i:nat{i <= length il}) (j:nat{j <= i}):
  Lemma (ensures (prefix (prefix il i) j == prefix il j))
        [SMTPat (prefix (prefix il i) j)]

val lemma_iseq_prefix_property (#a:_) (#n:_) (il: interleaving a n) (i:nat{i <= length il})
  : Lemma (ensures (SA.prefix (i_seq il) i = i_seq (prefix il i)))
          [SMTPat (prefix il i)]

val lemma_i2s_prefix_property (#a:_) (#n:_) (il:interleaving a n)(i:nat{i <= length il})(j:nat{j < i}):
  Lemma (ensures (i2s_map (prefix il i) j = i2s_map il j))
        [SMTPat (i2s_map (prefix il i) j)]

val lemma_iseq_append1 (#a #n:_) (il: interleaving a n) (x: elem_src a n)
  : Lemma (ensures (let il' = SA.append1 il x in
                    i_seq il' = SA.append1 (i_seq il) x.e))

let interleave (#a:eqtype) (s: seq a) (ss: sseq a)
  = exists (il: interleaving a (S.length ss)). (i_seq il = s) /\ (s_seq il = ss)

let empty_interleaving (a:eqtype) (n:nat)
  = Seq.empty #(elem_src a n)

val lemma_length0_implies_empty (#a:_) (#n:_) (il: interleaving a n{length il = 0})
  : Lemma (ensures (il == empty_interleaving a n))

val lemma_empty_sseq (a:eqtype) (n:_) (i: nat{i < n})
  : Lemma (ensures (let il = empty_interleaving a n in
                    S.index (s_seq il) i = Seq.empty #a))

val interleaving_snoc (#a #n:_) (il: interleaving a n{length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let ss = s_seq il in
                    let is = i_seq il in
                    let il' = prefix il i in
                    let ss' = s_seq il' in
                    let is' = i_seq il' in
                    let x = index il i in
                    let t = src il i in
                    i2s_map il i = (t,S.length (S.index ss' t)) /\
                    ss' == sseq_prefix ss t /\
                    is' = SA.prefix is i))

val interleaving_flat_length (#a #n:_) (il: interleaving a n)
  : Lemma (ensures (flat_length (s_seq il) = length il))

val lemma_interleave_extend
  (#a:eqtype) (#n:_)
  (ss: sseq a{S.length ss = n})
  (t: nat{t < n})
  (il': interleaving a n)
  : Lemma (requires (S.length (S.index ss t) > 0 /\ s_seq il' == sseq_prefix ss t))
          (ensures (let s = S.index ss t in
                    let i = S.length s - 1 in
                    let e = S.index s i in
                    let il = SA.append1 il' ({e;s=t}) in
                    s_seq il == ss))

val some_interleaving (#a: eqtype) (ss: sseq a)
  : il: interleaving a (S.length ss) {s_seq il = ss}
