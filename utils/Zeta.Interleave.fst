module Zeta.Interleave
module IF = Zeta.IdxFn

let gen_seq (a:eqtype) (n:_) =
  {
    seq_t = interleaving a n;
    IF.length = length;
    IF.prefix = prefix;
  }

let of_seq #a #n (t: nat) (il: interleaving a n) (i: seq_index il)
  = t = S.index il.ts i

let seq_i_fm a n (i:nat)
  : fm_t (gen_seq a n) a
  = FM (of_seq i) index

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
  = let t = sid il i in
    let fm = seq_i_fm a n t in
    let j = filter_map_map fm il i in
    (t,j)

let s2i_map (#a:_) (#n:_) (il:interleaving a n) (si: sseq_index (s_seq il))
  = let t,j = si in
    let fm = seq_i_fm a n t in
    filter_map_invmap fm il j

let lemma_i2s_s2i (#a:_) (#n:_) (il:interleaving a n) (i:seq_index il):
  Lemma (ensures (s2i_map il (i2s_map il i) = i))
  = ()

let lemma_index_prefix_property (#a #n:_) (il:interleaving a n) (i:nat{i <= length il}) (j:nat{j < i}):
  Lemma (ensures (index (prefix il i) j = index il j))
  = ()

let lemma_prefix_prefix_property (#a #n:_) (il:interleaving a n) (i:nat{i <= length il}) (j:nat{j <= i}):
  Lemma (ensures (prefix (prefix il i) j == prefix il j))
  = ()

let lemma_i2s_prefix_property (#a:_) (#n:_) (il:interleaving a n)(i:nat{i <= length il})(j:nat{j < i}):
  Lemma (ensures (i2s_map (prefix il i) j = i2s_map il j))
  = let t = sid il j in
    let fm = seq_i_fm a n t in
    filter_map_map_prefix_property fm il j i;
    admit()

let some_interleaving (#a:_) (ss: sseq a)
  : il: interleaving a (S.length ss) {s_seq il = ss}
  = admit()

let lemma_length0_implies_empty (#a #n:_) (il: interleaving a n{length il = 0})
  : Lemma (ensures (il == empty_interleaving a n))
  = admit()

let lemma_empty_sseq (a:eqtype) (n:_) (i: nat{i < n})
  : Lemma (ensures (let il = empty_interleaving a n in
                    S.index (s_seq il) i = empty #a))
  = admit()
