module Zeta.MultiSet.SSeq

let sseq2mset (#a:eqtype) (#f:cmp a) (s:sseq a) : mset a f
  = let open Zeta.Interleave in
    let il = some_interleaving s in
    seq2mset (i_seq il)

let lemma_interleaving_multiset (#a:_) (#f:cmp a) (#n:_) (il: interleaving a n)
  : Lemma (ensures (seq2mset #_ #f (i_seq il) == sseq2mset (s_seq il)))
  = admit()
