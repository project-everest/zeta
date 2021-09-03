module Zeta.Interleave

open FStar.Seq
open Zeta.SeqAux
open Zeta.SSeq
open Zeta.IdxFn

module S = FStar.Seq
module SA = Zeta.SeqAux

(* an interleaving of n sequences specifed by storing the mapping from every
 * interleaved element to the id of the originating sequence *)
type interleaving (a:eqtype) (n:nat) = {
  is: seq a;
  ts: s:seq (t:nat{t < n}) {S.length is = S.length s};
}

let i_seq (#a:_) (#n:nat) (il: interleaving a n)
  = il.is

let length (#a:_) (#n:_) (il: interleaving a n)
  = S.length il.is

let seq_index (#a:_) (#n:_) (il: interleaving a n) = i:nat{i < length il}

let index (#a:_) (#n:_) (il: interleaving a n) (i: seq_index il)
  = S.index (i_seq il) i

let sid (#a:_) (#n:_) (il: interleaving a n) (i: seq_index il)
  = S.index il.ts i

let prefix (#a:_) (#n:_) (il: interleaving a n) (i:nat{i <= length il})
  : il':interleaving a n {length il' = i}
  = {is = SA.prefix il.is i; ts = SA.prefix il.ts i}

val s_seq (#a:_) (#n:_) (il: interleaving a n): ss:sseq a{S.length ss = n}

val per_thread_prefix (#a:_) (#n:_) (il: interleaving a n) (i:nat{i <= length il})
  : Lemma (let ss = s_seq il in
           let il' = prefix il i in
           let ss' = s_seq il' in
           ss' `sseq_all_prefix_of` ss)

val i2s_map (#a:_) (#n:_) (il:interleaving a n) (i:seq_index il)
  : (si:sseq_index (s_seq il){index il i = indexss (s_seq il) si /\ fst si = sid il i})

val s2i_map (#a:eqtype) (#n:_) (il:interleaving a n) (si: sseq_index (s_seq il)):
  (i:seq_index il{index il i = indexss (s_seq il) si /\
                  i2s_map il i = si})

val lemma_i2s_s2i (#a:_) (#n:_) (il:interleaving a n) (i:seq_index il):
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

val lemma_i2s_prefix_property (#a:_) (#n:_) (il:interleaving a n)(i:nat{i <= length il})(j:nat{j < i}):
  Lemma (ensures (i2s_map (prefix il i) j = i2s_map il j))
        [SMTPat (i2s_map (prefix il i) j)]

let interleave (#a:eqtype) (s: seq a) (ss: sseq a)
  = exists (il: interleaving a (S.length ss)). (i_seq il = s) /\ (s_seq il = ss)

val some_interleaving (#a: eqtype) (ss: sseq a)
  : il: interleaving a (S.length ss) {s_seq il = ss}

let empty_interleaving (a:eqtype) (n:nat)
  = {is = empty #a; ts = empty #(t:nat{t < n})}

let lemma_empty_len (#a:_) (#n:_)
  : Lemma (ensures (length (empty_interleaving a n) = 0))
  = ()

val lemma_length0_implies_empty (#a:_) (#n:_) (il: interleaving a n{length il = 0})
  : Lemma (ensures (il == empty_interleaving a n))

val lemma_empty_sseq (a:eqtype) (n:_) (i: nat{i < n})
  : Lemma (ensures (let il = empty_interleaving a n in
                    S.index (s_seq il) i = empty #a))
