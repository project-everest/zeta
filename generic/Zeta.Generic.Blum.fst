module Zeta.Generic.Blum

let add_il (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : interleaving (ms_hashfn_dom vspec.app) n
  = admit()

let evict_il (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : interleaving (ms_hashfn_dom vspec.app) n
  = admit()

let lemma_add_evict_set_identical_glog (#vspec #n:_) (epmax: epoch) (il: verifiable_log vspec n)
  : Lemma (ensures (aems_equal_upto epmax il <==> G.aems_equal_upto epmax (to_glog il)))
  = admit()

let add_set_contains_each_add_elem (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il{is_blum_add il i})
  : Lemma (ensures (let be = blum_add_elem il i in
                    let ep = be.t.e in
                    add_set ep il `contains` be))
  = admit()

let some_add_elem_idx
  (#vspec #n:_)
  (il: verifiable_log vspec n)
  (be: ms_hashfn_dom vspec.app {let ep = be.t.e in
                                add_set ep il `contains` be})
  : i: seq_index il {is_blum_add il i /\ be = blum_add_elem il i}
  = admit()

let evict_set_contains_each_evict_elem (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il{is_blum_evict il i})
  : Lemma (ensures (let be = blum_evict_elem il i in
                    let ep = be.t.e in
                    evict_set ep il `contains` be))
  = admit()

let evict_set_is_a_set (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : Lemma (ensures (is_set (evict_set ep il)) )
  = admit()

let evict_elem_idx
  (#vspec #n:_)
  (il: verifiable_log vspec n)
  (be: ms_hashfn_dom vspec.app {let ep = be.t.e in
                                evict_set ep il `contains` be})
  : i: seq_index il {is_blum_evict il i /\ be = blum_evict_elem il i}
  = admit()

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

(* add elements of a specific key*)
let k_add_il (#vspec: verifier_spec) (#n:_) (ep: epoch) (gk: key vspec.app) (il: verifiable_log vspec n)
  : interleaving (ms_hashfn_dom vspec.app) n
  = admit()

let k_evict_il (#vspec: verifier_spec) (#n:_) (ep: epoch) (gk: key vspec.app) (il: verifiable_log vspec n)
  : interleaving (ms_hashfn_dom vspec.app) n
  = admit()


let add_set_rel_k_add_set
  (#vspec: verifier_spec)
  (#n:_)
  (ep: epoch)
  (gk: key vspec.app)
  (il: verifiable_log vspec n)
  (be: ms_hashfn_dom vspec.app {let gkc,_ = be.r in gkc = gk})
  : Lemma (ensures (mem be (k_add_set ep gk il) = mem be (add_set ep il)))
  = admit()

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
