module Zeta.Interleave
open Zeta.IdxFn

module IF = Zeta.IdxFn

let seq_index = SA.seq_index

let gen_seq (a:eqtype) (n:_) =
  {
    seq_t = interleaving a n;
    IF.length = S.length;
    IF.prefix = SA.prefix;
  }

(* an element is from src t *)
let from_src #a #n (t: nat) (il: interleaving a n) (i: seq_index il)
  = t = (S.index il i).s

let to_elem #a #n (il: interleaving a n) (i: seq_index il)
  = (S.index il i).e

let i_seq (#a:_) (#n:nat) (il: interleaving a n)
  = map #(gen_seq a n) (to_elem #a #n) il

let index_prop (#a #n:_) (il: interleaving a n) (i: SA.seq_index il)
  : Lemma (ensures ((S.index il i).e = index il i))
  = admit()

let seq_i_fm (a:eqtype) n (i:nat)
  : fm_t (gen_seq a n) a
  = FM (from_src i) to_elem

let s_seq_i (#a:_) (#n:_) (il: interleaving a n) (i:nat{i < n})
  = filter_map (seq_i_fm a n i) il

let s_seq (#a:_) (#n:_) (il: interleaving a n)
  = init n (s_seq_i il)

let per_thread_prefix (#a:_) (#n:_) (il: interleaving a n) (i:nat{i <= length il})
  : Lemma (let ss = s_seq il in
           let il' = prefix il i in
           let ss' = s_seq il' in
           ss' `sseq_all_prefix_of` ss)
  = admit()

let i2s_map (#a:_) (#n:_) (il:interleaving a n) (i:seq_index il)
  = let t = src il i in
    let fm = seq_i_fm a n t in
    let j = filter_map_map fm il i in
    lemma_map_map #(gen_seq a n) (to_elem #a #n) il i;
    (t,j)

let i2s_map_monotonic (#a #n:_) (il: interleaving a n) (i j: SA.seq_index il)
  : Lemma (requires (src il i = src il j))
          (ensures ((i < j ==> snd (i2s_map il i) < snd (i2s_map il j)) /\
                    (j < i ==> snd (i2s_map il j) < snd (i2s_map il i))))
  = admit()

let s2i_map (#a:_) (#n:_) (il:interleaving a n) (si: sseq_index (s_seq il))
  = let t,j = si in
    let fm = seq_i_fm a n t in
    let i = filter_map_invmap fm il j in
    lemma_map_map #(gen_seq a n) (to_elem #a #n) il i;
    i

let s2i_map_monotonic (#a #n:_) (il: interleaving a n) (i j: sseq_index (s_seq il))
  : Lemma (requires (fst i = fst j))
          (ensures ((snd i < snd j ==> s2i_map il i < s2i_map il j) /\
                    (snd j < snd i ==> s2i_map il j < s2i_map il i)))
  = admit()

let lemma_i2s_s2i (#a:_) (#n:_) (il:interleaving a n) (i:seq_index il):
  Lemma (ensures (s2i_map il (i2s_map il i) = i))
  = ()

let lemma_index_prefix_property (#a #n:_) (il:interleaving a n) (i:nat{i <= length il}) (j:nat{j < i}):
  Lemma (ensures (index (prefix il i) j = index il j))
  = lemma_map_map #(gen_seq a n) (to_elem #a #n) il j;
    let fm = map_fm #(gen_seq a n) #_ (to_elem #a #n)   in
    filter_map_map_prefix_property fm il j i;
    ()

let lemma_prefix_prefix_property (#a #n:_) (il:interleaving a n) (i:nat{i <= length il}) (j:nat{j <= i}):
  Lemma (ensures (prefix (prefix il i) j == prefix il j))
  = ()

let lemma_iseq_prefix_property (#a:_) (#n:_) (il: interleaving a n) (i:nat{i <= length il})
  : Lemma (ensures (SA.prefix (i_seq il) i = i_seq (prefix il i)))
  = admit()

let lemma_i2s_prefix_property (#a:_) (#n:_) (il:interleaving a n)(i:nat{i <= length il})(j:nat{j < i}):
  Lemma (ensures (i2s_map (prefix il i) j = i2s_map il j))
  = let t = src il j in
    let fm = seq_i_fm a n t in
    filter_map_map_prefix_property fm il j i;
    ()

let lemma_iseq_append1 (#a #n:_) (il: interleaving a n) (x: elem_src a n)
  : Lemma (ensures (let il' = SA.append1 il x in
                    i_seq il' = SA.append1 (i_seq il) x.e))
  = admit()

let some_interleaving (#a:_) (ss: sseq a)
  : il: interleaving a (S.length ss) {s_seq il = ss}
  = admit()

let lemma_length0_implies_empty (#a #n:_) (il: interleaving a n{length il = 0})
  : Lemma (ensures (il == empty_interleaving a n))
  = admit()

let lemma_empty_sseq (a:eqtype) (n:_) (i: nat{i < n})
  : Lemma (ensures (let il = empty_interleaving a n in
                    S.index (s_seq il) i = S.empty #a))
  = admit()

let interleaving_snoc (#a #n:_) (il: interleaving a n{length il > 0})
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
  = admit()

let interleaving_flat_length (#a #n:_) (il: interleaving a n)
  : Lemma (ensures (flat_length (s_seq il) = length il))
  = admit()
