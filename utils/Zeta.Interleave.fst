module Zeta.Interleave

let elem #a #n (e: (a & t:nat {t < n})): a
  = fst e

let i_seq_base (#a:_) (il: interleaving a)
  = simple_map elem il.st

let lemma_iseq_length (#a:_) (il: interleaving a)
  : Lemma (ensures (S.length il.st = S.length (i_seq_base il)))
          [SMTPat (i_seq_base il)]
  = admit()

let i_seq (#a:_) (il: interleaving a): (s: seq a {S.length il.st = S.length s})
  = i_seq_base il

let seq_id #a #n (e: (a & t:nat{t < n}))
  = snd e

let of_seq_id #a #n (t:nat{t < n}) (e: (a & t:nat{ t < n }))
  = seq_id e = t

let s_seq_i (#a:_) (il: interleaving a) (i:nat{i < il.n})
  = simple_filter_map (of_seq_id i) elem il.st

let s_seq (#a:_) (il: interleaving a)
  = init il.n (s_seq_i il)

let lemma_index (#a:_) (il: interleaving a) (i: seq_index il)
  : Lemma (ensures (index il i = elem (S.index il.st i)))
          [SMTPat (index il i)]
  = admit()

let prefix_base (#a:_) (il: interleaving a) (i:nat{i <= length il})
  = {n = il.n; st = SA.prefix il.st i}

let lemma_prefix #a (il: interleaving a) (i:nat{i <= length il})
  : Lemma (ensures (i_seq (prefix_base il i) = SA.prefix (i_seq il) i))
          [SMTPat (prefix_base il i)]
  = admit()

let prefix (#a:_) (il: interleaving a) (i:nat{i <= length il})
  = prefix_base il i

let per_thread_prefix (#a:eqtype) (il: interleaving a) (i:nat{i <= length il})
  : Lemma (let ss = s_seq il in
           let il' = prefix il i in
           let ss' = s_seq il' in
           ss' `sseq_all_prefix_of` ss)
  = admit()

let i2s_map (#a:_) (il:interleaving a) (i:seq_index il)
  = let t = seq_id (S.index il.st i) in
    let fm = simple_fm_t (of_seq_id t) (elem #a #il.n) in
    let j = filter_map_map fm il.st i in
    (t,j)

let s2i_map (#a:eqtype) (il:interleaving a) (si: sseq_index (s_seq il))
  = let t,j = si in
    let fm = simple_fm_t (of_seq_id t) (elem #a #il.n) in
    filter_map_invmap fm il.st j

let lemma_i2s_s2i (#a:eqtype) (il:interleaving a) (i:seq_index il):
  Lemma (ensures (s2i_map il (i2s_map il i) = i))
  = ()

let prefix_identity (#a:eqtype) (il:interleaving a)
  : Lemma (ensures prefix il (length il) == il)
  = ()

let lemma_prefix_index (#a:eqtype) (il:interleaving a) (i:nat{i <= length il}) (j:nat{j < i}):
  Lemma (ensures (index (prefix il i) j = index il j))
  = ()

let lemma_prefix_prefix (#a:eqtype) (il:interleaving a) (i:nat{i <= length il}) (j:nat{j <= i}):
  Lemma (ensures (prefix (prefix il i) j == prefix il j))
  = admit()

let some_interleaving (#a: eqtype) (ss: sseq a)
  : il: interleaving a {s_seq il = ss}
  = admit()
