module Zeta.Generic.Interleave


let lemma_prefix_verifiable (#vspec:_) (n:_) (il:verifiable_log vspec n) (i:nat{i <= S.length il}):
  Lemma (ensures (verifiable (I.prefix il i)))
  = admit()

let idxn_has_prefix_prop (#vspec:_) (#n:nat) (#b:_) (tfn: T.idxfn_t vspec b)
  : Lemma (ensures (IF.prefix_property #(gen_seq vspec n) (idxfn_base #_ #n #_ tfn)))
  = admit()

let idxfn_prefix_property (#vspec:_) (#n:_) (#b:_) (tfn: T.idxfn_t vspec b)
  (il: verifiable_log vspec n) (j:nat{j <= S.length il}) (i: nat{i < j})
  : Lemma (ensures (idxfn tfn il i == idxfn tfn (prefix il j) i))
  = admit()

let idxfnil_prefix_property (#vspec:_) (#n:_) (#b:eqtype) (tfn: T.idxfn_t vspec b)
  (il: verifiable_log vspec n) (j:nat{j <= S.length il}) (i: nat{i < j})
  : Lemma (ensures (idxfn_il tfn il i == idxfn_il tfn (prefix il j) i))
  = admit()

let cond_idxfn_has_prefix_prop (#vspec #n #b #f:_) (m: T.cond_idxfn_t b f)
  : Lemma (ensures (IF.cond_prefix_property #(gen_seq vspec n) #_ #(idxfn f) (cond_idxfn_base m)))
  = admit()

let lemma_filter_map (#vspec #n:_) (#b:eqtype) (#f:_) (m: T.cond_idxfn_t b f)
    (il: verifiable_log vspec n) (i: seq_index il)
  : Lemma (ensures (let fmil = to_fm (cond_idxfn_il #vspec #n #_ #_ m) in
                    let ilb = IF.filter_map fmil il in
                    let fm = to_fm m in
                    let ssb = SF.filter_map (G.gen_sseq vspec) fm (to_glog il) in
                    let fmil2 = to_fm (cond_idxfn #vspec #n #_ #_ m) in
                    let sb = IF.filter_map fmil2 il in
                    ssb = s_seq ilb /\
                    sb = i_seq ilb))
  = admit()

let thread_state_pre (#vspec: verifier_spec) (#n:_) (tid:nat{tid < n})
  : IF.idxfn_t (gen_seq vspec n) (v:vspec.vtls_t {vspec.valid v})
  = admit()

let thread_state_post (#vspec: verifier_spec) (#n:_) (tid:nat{tid < n})
  : IF.idxfn_t (gen_seq vspec n) (v:vspec.vtls_t {vspec.valid v})
  = admit()
