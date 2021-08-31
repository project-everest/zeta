module Zeta.MultiSet.SSeq

let sseq2mset (#a:eqtype) (#f:cmp a) (s:sseq a) : mset a f
  = let open Zeta.Interleave in
    let il = some_interleaving s in
    seq2mset (i_seq il)
