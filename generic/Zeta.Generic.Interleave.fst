module Zeta.Generic.Interleave


let lemma_prefix_verifiable (#vspec:_) (n:_) (il:verifiable_log vspec n) (i:nat{i <= S.length il}):
  Lemma (ensures (verifiable (I.prefix il i)))
  = admit()

let idxn_has_prefix_prop (#vspec:_) (#n:nat) (#b:_) (tfn: T.idxfn_t vspec b)
  : Lemma (ensures (IF.prefix_property #(gen_seq vspec n) (idxfn_base #_ #n #_ tfn)))
  = admit()

let idxfn_prefix_property (#vspec:_) (#n:_) (#b:_) (tfn: T.idxfn_t vspec b)
  (il: verifiable_log vspec n) (j:nat{j <= S.length il}) (i: nat{i < j})
  : Lemma (ensures (idxfn tfn il i = idxfn tfn (prefix il j) i))
  = admit()

let cond_idxfn_has_prefix_prop (#vspec #n #b #f:_) (m: T.cond_idxfn_t b f)
  : Lemma (ensures (IF.cond_prefix_property #(gen_seq vspec n) #_ #(idxfn f) (cond_idxfn_base m)))
  = admit()

(*
  let gs = gen_seq vspec n in
    //let b = timestamp in
    let f: IF.idxfn_t gs _ = clock #vspec #n in
    let s: gs.seq_t = il in
    //assert(IF.prefix_property f);
    //assert(j <= gs.length s);
    //assert(i < j);
    assert(f s i = f (gs.prefix s j) i);
    //assert(f s i = clock il i);
    //assert(f (gs.prefix s j) i = clock (prefix il j) i);
    ()
    *)
