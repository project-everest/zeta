module Zeta.MultiSet.SSeq

open FStar.Classical
open FStar.Seq
open Zeta.SeqAux

let sseq2mset (#a:eqtype) (#f:cmp a) (s:sseq a) : mset a f
  = let open Zeta.Interleave in
    let il = some_interleaving s in
    seq2mset (i_seq il)

let si_seq (#a #n:_) (il: interleaving a n)
  = i_seq (some_interleaving (s_seq il))

let si_seq_length (#a #n:_) (il: interleaving a n)
  : Lemma (ensures (length il = length (si_seq il)))
          [SMTPat (si_seq il)]
  = let ss = s_seq il in
    let il2 = some_interleaving ss in
    interleaving_flat_length il;
    interleaving_flat_length il2

let i2si (#a #n:_) (il: interleaving a n) (i: seq_index il)
  : j:seq_index (si_seq il){index (i_seq il) i = index (si_seq il) j}
  = let is = i_seq il in
    let ss = s_seq il in
    let il2 = some_interleaving ss in
    let ii = i2s_map il i in
    s2i_map il2 ii

let i2si_prop_aux #a #n (il: interleaving a n) (i1 i2: seq_index il)
  : Lemma (ensures (i1 =!= i2 ==> i2si il i1 =!= i2si il i2))
  = let ss = s_seq il in
    let il2 = some_interleaving ss in
    if i1 <> i2 then
      let ii1 = i2s_map il i1 in
      let ii2 = i2s_map il i2 in

      if src il i1 = src il i2 then (
        i2s_map_monotonic il i1 i2;
        s2i_map_monotonic il2 ii1 ii2
      )

let i2si_prop #a #n (il: interleaving a n)
  : Lemma (ensures (let s1 = i_seq il in
                    let s2 = si_seq il in
                    let f:smap s1 s2 = i2si il in
                    forall (i j: seq_index s1). (i =!= j) ==> f i =!= f j))
          [SMTPat (i2si il)]
  = forall_intro_2 (i2si_prop_aux il)

let i2si_into #a #n (il: interleaving a n)
  : into_smap (i_seq il) (si_seq il)
  = i2si il

let si2i (#a #n:_) (il: interleaving a n) (j: seq_index (si_seq il))
  : i:seq_index il{index (i_seq il) i = index (si_seq il) j}
  = let is = i_seq il in
    let ss = s_seq il in
    let il2 = some_interleaving ss in
    let jj = i2s_map il2 j in
    s2i_map il jj

let si2i_prop_aux #a #n (il: interleaving a n) (j1 j2: seq_index (si_seq il))
  : Lemma (ensures (j1 =!= j2 ==> si2i il j1 =!= si2i il j2))
  = let ss = s_seq il in
    let il2 = some_interleaving ss in
    if j1 <> j2 then
      let jj1 = i2s_map il2 j1 in
      let jj2 = i2s_map il2 j2 in

      if src il2 j1 = src il2 j2 then (
        i2s_map_monotonic il2 j1 j2;
        s2i_map_monotonic il jj1 jj2
      )

let si2i_prop #a #n (il: interleaving a n)
  : Lemma (ensures (let s1 = i_seq il in
                    let s2 = si_seq il in
                    let f:smap s2 s1 = si2i il in
                    forall (i j: seq_index s1). (i =!= j) ==> f i =!= f j))
          [SMTPat (si2i il)]
  = forall_intro_2 (si2i_prop_aux il)

let si2i_into #a #n (il: interleaving a n)
  : into_smap (si_seq il) (i_seq il)
  = si2i il

let lemma_interleaving_multiset (#a:_) (#f:cmp a) (#n:_) (il: interleaving a n)
  : Lemma (ensures (seq2mset #_ #f (i_seq il) == sseq2mset (s_seq il)))
  = let ss = s_seq il in
    let il2 = some_interleaving ss in
    bijection_seq_mset #a #f (i_seq il) (si_seq il) (i2si_into il) (si2i_into il)