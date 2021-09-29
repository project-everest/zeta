module Zeta.Generic.Blum

module IF = Zeta.IdxFn

let gen_seq (vspec n:_) = {
  IF.seq_t = verifiable_log vspec n;
  IF.length = length;
  IF.prefix = prefix;
}

(* is this a blum add within epoch ep *)
let is_blum_add_epoch (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (i: seq_index il)
  = is_blum_add il i &&
    (let be = blum_add_elem il i in
     be.t.e = ep)

let is_blum_add_epoch_ifn (#vspec #n:_) (ep: epoch)
  : IF.idxfn_t (gen_seq vspec n) bool
  = is_blum_add_epoch #vspec #n ep

let is_blum_add_ifn (#vspec #n:_)
  : IF.idxfn_t (gen_seq vspec n) bool
  = is_blum_add #vspec #n

let blum_add_elem_ifn (#vspec #n:_)
  : IF.cond_idxfn_t (ms_hashfn_dom vspec.app) (is_blum_add_ifn #vspec #n)
  = blum_add_elem #vspec #n

let blum_add_elem_src (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il{is_blum_add il i})
  : elem_src (ms_hashfn_dom vspec.app) n
  = let e = blum_add_elem il i in
    let s = src il i in
    {e ; s}

let blum_add_elem_src_ifn (#vspec #n:_)
  : IF.cond_idxfn_t (elem_src (ms_hashfn_dom vspec.app) n) (is_blum_add_ifn #vspec #n)
  = blum_add_elem_src #vspec #n

let add_il (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : interleaving (ms_hashfn_dom vspec.app) n
  = let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec #n ep) (blum_add_elem_src_ifn #vspec #n) in
    IF.filter_map fm il

let is_blum_evict_epoch (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (i: seq_index il)
  = is_blum_evict il i &&
    (let be = blum_evict_elem il i in
     be.t.e = ep)

let is_blum_evict_epoch_ifn (#vspec #n:_) (ep: epoch)
  : IF.idxfn_t (gen_seq vspec n) bool
  = is_blum_evict_epoch #vspec #n ep

let is_blum_evict_ifn (#vspec #n:_)
  : IF.idxfn_t (gen_seq vspec n) bool
  = is_blum_evict #vspec #n

let blum_evict_elem_ifn (#vspec #n:_)
  : IF.cond_idxfn_t (ms_hashfn_dom vspec.app) (is_blum_evict_ifn #vspec #n)
  = blum_evict_elem #vspec #n

let blum_evict_elem_src (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il{is_blum_evict il i})
  : elem_src (ms_hashfn_dom vspec.app) n
  = let e = blum_evict_elem il i in
    let s = src il i in
    { e; s }

let blum_evict_elem_src_ifn (#vspec #n:_)
  : IF.cond_idxfn_t (elem_src (ms_hashfn_dom vspec.app) n) (is_blum_evict_ifn #vspec #n)
  = blum_evict_elem_src #vspec #n

let evict_il (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : interleaving (ms_hashfn_dom vspec.app) n
  = let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec #n ep) (blum_evict_elem_src_ifn #vspec #n) in
    IF.filter_map fm il

let lemma_add_evict_set_identical_glog (#vspec #n:_) (epmax: epoch) (il: verifiable_log vspec n)
  : Lemma (ensures (aems_equal_upto epmax il <==> G.aems_equal_upto epmax (to_glog il)))
  = admit()

let add_set_contains_each_add_elem (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il{is_blum_add il i})
  : Lemma (ensures (let be = blum_add_elem il i in
                    let ep = be.t.e in
                    add_set ep il `contains` be))
  = let be = blum_add_elem il i in
    let ep = be.t.e in
    let ail = add_il ep il in
    let asq = i_seq ail in
    let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec #n ep) (blum_add_elem_src_ifn #vspec #n) in
    let j = IF.filter_map_map fm il i in

    index_prop ail j;
    assert(S.index asq j = be);
    mset_contains_seq_element #_ #(ms_hashfn_dom_cmp vspec.app) asq j

let some_add_elem_idx
  (#vspec #n:_)
  (il: verifiable_log vspec n)
  (be: ms_hashfn_dom vspec.app {let ep = be.t.e in
                                add_set ep il `contains` be})
  : i: seq_index il {is_blum_add il i /\ be = blum_add_elem il i}
  = let ep = be.t.e in
    let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec #n ep) (blum_add_elem_src_ifn #vspec #n) in
    let ail = add_il ep il in
    let asq = i_seq ail in
    let j = index_of_mselem #_ #(ms_hashfn_dom_cmp vspec.app) asq be in
    let i = IF.filter_map_invmap fm il j in
    index_prop ail j;
    i

let evict_set_contains_each_evict_elem (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il{is_blum_evict il i})
  : Lemma (ensures (let be = blum_evict_elem il i in
                    let ep = be.t.e in
                    evict_set ep il `contains` be))
  = let be = blum_evict_elem il i in
    let ep = be.t.e in
    let eil = evict_il ep il in
    let es = i_seq eil in
    let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec #n ep) (blum_evict_elem_src_ifn #vspec #n) in
    let j = IF.filter_map_map fm il i in
    index_prop eil j;
    mset_contains_seq_element #_ #(ms_hashfn_dom_cmp vspec.app) es j

let evict_set_is_a_set (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : Lemma (ensures (is_set (evict_set ep il)) )
  = admit()

let evict_elem_idx
  (#vspec #n:_)
  (il: verifiable_log vspec n)
  (be: ms_hashfn_dom vspec.app {let ep = be.t.e in
                                evict_set ep il `contains` be})
  : i: seq_index il {is_blum_evict il i /\ be = blum_evict_elem il i}
  = let ep = be.t.e in
    let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec #n ep) (blum_evict_elem_src_ifn #vspec #n) in
    let eil = evict_il ep il in
    let es = i_seq eil in
    let j = index_of_mselem #_ #(ms_hashfn_dom_cmp vspec.app) es be in
    let i = IF.filter_map_invmap fm il j in
    index_prop eil j;
    i

let lemma_evict_before_add (#vspec #n:_) (itsl: its_log vspec n) (i:seq_index itsl{is_blum_add itsl i}):
  Lemma (ensures (let be = blum_add_elem itsl i in
                  let ep = be.t.e in
                  not (evict_set ep itsl `contains` be) \/
                  evict_elem_idx itsl be < i))
 = admit()

(* a slightly different version of of the previous lemma - the count of an add element
 * in the evict set is the same in the prefix as the full sequence *)
let lemma_evict_before_add2
  (#vspec #n:_)
  (ep: epoch)
  (itsl: its_log vspec n)
  (i:nat{i <= length itsl})
  (be: ms_hashfn_dom vspec.app)
  : Lemma (requires (let itsli = prefix itsl i in
                     let as = add_set ep itsli in
                     let es = evict_set ep itsli in
                     mem be as > mem be es))
          (ensures (let as = add_set ep itsl in
                    let es = evict_set ep itsl in
                    mem be as > mem be es))
  = admit()

let lemma_evict_before_add3 (#vspec #n:_) (itsl: its_log vspec n) (i: seq_index itsl) (j:seq_index itsl):
  Lemma (requires (is_blum_add itsl i /\
                   is_blum_evict itsl j /\
                   blum_add_elem itsl i = blum_evict_elem itsl j))
        (ensures (j < i))
  = admit()

let lemma_add_set_mem (#vspec #n:_) (il: verifiable_log vspec n) (i1 i2: seq_index il)
  : Lemma (requires (i1 <> i2 /\ is_blum_add il i1 /\ is_blum_add il i2 /\
                     blum_add_elem il i1 = blum_add_elem il i2))
          (ensures (let be = blum_add_elem il i1 in
                    let ep = be.t.e in
                    mem be (add_set ep il) >= 2))
  = admit()

let is_blum_add_of_key (#vspec: verifier_spec) (#n:_) (ep: epoch) (gk: key vspec.app)
  (il: verifiable_log vspec n) (i: seq_index il)
  = is_blum_add il i &&
    (let be = blum_add_elem il i in
     be.t.e = ep && fst be.r = gk)

let is_blum_add_of_key_ifn (#vspec: verifier_spec) (#n:_) (ep: epoch) (gk: key vspec.app)
  : IF.idxfn_t (gen_seq vspec n) bool
  = is_blum_add_of_key #vspec #n ep gk

let is_blum_evict_of_key (#vspec: verifier_spec) (#n:_) (ep: epoch) (gk: key vspec.app)
  (il: verifiable_log vspec n) (i: seq_index il)
  = is_blum_evict il i &&
    (let be = blum_evict_elem il i in
     be.t.e = ep && fst be.r = gk)

let is_blum_evict_of_key_ifn (#vspec: verifier_spec) (#n:_) (ep: epoch) (gk: key vspec.app)
  : IF.idxfn_t (gen_seq vspec n) bool
  = is_blum_evict_of_key #vspec #n ep gk

(* add elements of a specific key*)
let k_add_il (#vspec: verifier_spec) (#n:_) (ep: epoch) (gk: key vspec.app) (il: verifiable_log vspec n)
  : interleaving (ms_hashfn_dom vspec.app) n
  = let fm = IF.to_fm (is_blum_add_of_key_ifn #vspec #n ep gk) (blum_add_elem_src_ifn #vspec #n) in
    IF.filter_map fm il

let k_evict_il (#vspec: verifier_spec) (#n:_) (ep: epoch) (gk: key vspec.app) (il: verifiable_log vspec n)
  : interleaving (ms_hashfn_dom vspec.app) n
  = let fm = IF.to_fm (is_blum_evict_of_key_ifn #vspec #n ep gk) (blum_evict_elem_src_ifn #vspec #n) in
    IF.filter_map fm il

let add_set_rel_k_add_set
  (#vspec: verifier_spec)
  (#n:_)
  (ep: epoch)
  (gk: key vspec.app)
  (il: verifiable_log vspec n)
  (be: ms_hashfn_dom vspec.app {let gkc,_ = be.r in gkc = gk})
  : Lemma (ensures (mem be (k_add_set ep gk il) = mem be (add_set ep il)))
  = let ast = add_set ep il in
    let astk = k_add_set ep gk il in
    admit()


let evict_set_rel_k_evict_set
  (#vspec: verifier_spec)
  (#n:_)
  (ep: epoch)
  (gk: key vspec.app)
  (il: verifiable_log vspec n)
  (be: ms_hashfn_dom vspec.app{let gkc,_ = be.r in gkc = gk})
  : Lemma (ensures (mem be (k_evict_set ep gk il) = mem be (evict_set ep il)))
  = admit()

let k_add_set_correct
  (#vspec: verifier_spec)
  (#n:_)
  (ep: epoch)
  (gk: key vspec.app)
  (il: verifiable_log vspec n {length il > 0})
  (be: ms_hashfn_dom vspec.app)
  : Lemma (ensures (let gkc,_ = be.r in
                    k_add_set ep gk il `contains` be ==> gkc = gk /\ be.t.e = ep))
  = admit()

let k_evict_set_correct
  (#vspec: verifier_spec)
  (#n:_)
  (ep: epoch)
  (gk: key vspec.app)
  (il: verifiable_log vspec n {length il > 0})
  (be: ms_hashfn_dom vspec.app)
  : Lemma (ensures (let gkc,_ = be.r in
                    k_evict_set ep gk il `contains` be ==> gkc = gk /\ be.t.e = ep))
  = admit()

let k_add_set_empty
  (#vspec: verifier_spec)
  (#n:_)
  (ep: epoch)
  (gk: key vspec.app)
  (il: verifiable_log vspec n {length il = 0})
  : Lemma (ensures (k_add_set ep gk il == empty))
  = admit()

(* if the tail element is a blum add, then the add set is obtained by adding that
 * blum add to the prefix *)
let k_add_set_snoc
  (#vspec: verifier_spec)
  (#n:_)
  (ep: epoch)
  (gk: key vspec.app)
  (il: verifiable_log vspec n {length il > 0})
  : Lemma (ensures (let n = length il in
                    let il' = prefix il (n- 1 ) in
                    let b = is_blum_add_of_key ep gk il (n - 1) in
                    let as' = k_add_set ep gk il' in
                    let as = k_add_set ep gk il in
                    (b ==> as == add_elem as' (blum_add_elem il (n - 1))) /\
                    (~b ==> as == as')))
  = admit()

let k_evict_set_empty
  (#vspec: verifier_spec)
  (#n:_)
  (ep: epoch)
  (gk: key vspec.app)
  (il: verifiable_log vspec n {length il = 0})
  : Lemma (ensures (k_evict_set ep gk il == empty))
  = admit()

(* analogous theorem for evict sets*)
let k_evict_set_snoc
  (#vspec: verifier_spec)
  (#n:_)
  (ep: epoch)
  (gk: key vspec.app)
  (il: verifiable_log vspec n {length il > 0})
  : Lemma (ensures (let n = length il in
                    let il' = prefix il (n- 1 ) in
                    let b = is_blum_evict_of_key ep gk il (n - 1) in
                    let as' = k_evict_set ep gk il' in
                    let as = k_evict_set ep gk il in
                    (b ==> as == add_elem as' (blum_evict_elem il (n - 1))) /\
                    (~b ==> as == as')))
  = admit()
