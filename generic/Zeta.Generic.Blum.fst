module Zeta.Generic.Blum

open Zeta.SMap
open FStar.Classical

module IF = Zeta.IdxFn
module T = Zeta.Generic.Thread

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

let t_add_seq_il (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (t:nat {t < n})
  = let a_il = add_il ep il in
    let a_ss = s_seq a_il in
    S.index a_ss t

let t_add_seq_gl (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (t: nat{t < n})
  = let gl = s_seq il in
    let tl = G.index gl t in
    T.add_seq ep tl

#push-options "--fuel 0 --ifuel 1 --query_stats"

let t_add_i2g (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (t:nat{t < n})
  (i:SA.seq_index (t_add_seq_il ep il t))
  : j:SA.seq_index (t_add_seq_gl ep il t){S.index (t_add_seq_il ep il t) i = S.index (t_add_seq_gl ep il t) j}
  = let ta_il = t_add_seq_il ep il t in
    let ta_gl = t_add_seq_gl ep il t in
    let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec #n ep) (blum_add_elem_src_ifn #vspec #n) in
    let a_il = add_il ep il in
    let gl = to_glog il in
    let tl = G.index gl t in

    (* index in the add seq sequence *)
    let i1 = s2i_map a_il (t,i) in
    assert(i2s_map a_il i1 = (t,i));
    assert(src a_il i1 = t);

    (* index in the interleaved sequence il *)
    let i2 = IF.filter_map_invmap fm il i1 in
    assert(blum_add_elem il i2 = S.index ta_il i);
    assert(src il i2 = t);

    (* index in the original log of the t'th thread *)
    let _,i3 = i2s_map il i2 in
    assert(T.blum_add_elem tl i3 = blum_add_elem il i2);

    (* map i3 to the add seq - the index with ta_gl *)
    T.add_seq_map tl i3

let t_add_i2g_mono (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (t:nat{t < n})
  : Lemma (ensures (monotonic_prop (t_add_i2g ep il t)))
          [SMTPat (t_add_i2g ep il t)]
  = let ta_il = t_add_seq_il ep il t in
    let ta_gl = t_add_seq_gl ep il t in
    let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec #n ep) (blum_add_elem_src_ifn #vspec #n) in
    let a_il = add_il ep il in
    let gl = to_glog il in
    let tl = G.index gl t in

    let f = t_add_i2g ep il t in

    let aux (i j: SA.seq_index ta_il)
      : Lemma (ensures (i < j ==> f i < f j))
      = if i < j then (
          let i1 = s2i_map a_il (t,i) in
          let j1 = s2i_map a_il (t,j) in
          s2i_map_monotonic a_il (t,i) (t,j);
          assert(i1 < j1);

          let i2 = IF.filter_map_invmap fm il i1 in
          let j2 = IF.filter_map_invmap fm il j1 in
          IF.filter_map_invmap_monotonic fm il i1 j1;
          assert(i2 < j2);

          let _,i3 = i2s_map il i2 in
          let _,j3 = i2s_map il j2 in
          i2s_map_monotonic il i2 j2;
          assert(i3 < j3);

          T.add_seq_map_monotonic tl i3 j3
        )
    in
    forall_intro_2 aux

let t_add_g2i (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (t:nat{t < n})
  (j:SA.seq_index (t_add_seq_gl ep il t))
  : i:SA.seq_index (t_add_seq_il ep il t){S.index (t_add_seq_il ep il t) i = S.index (t_add_seq_gl ep il t) j}
  = let ta_il = t_add_seq_il ep il t in
    let ta_gl = t_add_seq_gl ep il t in
    let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec #n ep) (blum_add_elem_src_ifn #vspec #n) in
    let a_il = add_il ep il in
    let gl = to_glog il in
    let tl = G.index gl t in

    let j1 = T.add_seq_invmap ep tl j in
    let j2 = s2i_map il (t,j1) in
    assert(is_blum_add il j2);
    assert(blum_add_elem il j2 = T.blum_add_elem tl j1);
    let j3 = IF.filter_map_map fm il j2 in
    let _,j4 = i2s_map a_il j3 in
    j4

let t_add_g2i_mono (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (t:nat{t < n})
  : Lemma (ensures (monotonic_prop (t_add_g2i ep il t)))
  = let ta_il = t_add_seq_il ep il t in
    let ta_gl = t_add_seq_gl ep il t in
    let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec #n ep) (blum_add_elem_src_ifn #vspec #n) in
    let a_il = add_il ep il in
    let gl = to_glog il in
    let tl = G.index gl t in

    let f = t_add_g2i ep il t in
    let aux (i j: SA.seq_index ta_gl)
      : Lemma (ensures (i < j ==> f i < f j))
      = if i < j then (
          let i1 = T.add_seq_invmap ep tl i in
          let j1 = T.add_seq_invmap ep tl j in
          T.add_seq_invmap_monotonic ep tl i j;
          assert(i1 < j1);

          let i2 = s2i_map il (t,i1) in
          let j2 = s2i_map il (t,j1) in
          s2i_map_monotonic il (t,i1) (t,j1);
          assert(i2 < j2);

          let i3 = IF.filter_map_map fm il i2 in
          let j3 = IF.filter_map_map fm il j2 in
          IF.lemma_filter_map_map_monotonic fm il i2 j2;
          assert(i3 < j3);

          i2s_map_monotonic a_il i3 j3
        )
    in
    forall_intro_2 aux

#pop-options

#push-options "--z3rlimit_factor 3"

let add_seq_identical_thread (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (t: nat{t < n})
  : Lemma (ensures (t_add_seq_il ep il t == t_add_seq_gl ep il t))
   = monotonic_bijection_implies_equal
      (t_add_seq_il ep il t)
      (t_add_seq_gl ep il t)
      (t_add_i2g ep il t)
      (t_add_g2i ep il t)

#pop-options

#push-options "--fuel 0 --ifuel 1 --query_stats"

let add_sseq_identical (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : Lemma (ensures (s_seq (add_il ep il) == G.add_sseq ep (to_glog il)))
  = let a_il = add_il ep il in
    let a_ss1 = s_seq a_il in
    let gl = to_glog il in
    let a_ss2 = G.add_sseq ep gl in

    let aux (t:_)
      : Lemma (ensures (S.index a_ss1 t == S.index a_ss2 t))
      = add_seq_identical_thread ep il t
    in
    forall_intro aux;
    assert(S.equal a_ss1 a_ss2)

let add_set_identical (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : Lemma (ensures (add_set ep il == G.add_set ep (to_glog il)))
  = add_sseq_identical ep il;
    Zeta.MultiSet.SSeq.lemma_interleaving_multiset #_ #(ms_hashfn_dom_cmp vspec.app) (add_il ep il)

#pop-options

let t_evict_seq_il (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (t:nat {t < n})
  = let a_il = evict_il ep il in
    let a_ss = s_seq a_il in
    S.index a_ss t

let t_evict_seq_gl (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (t: nat{t < n})
  = let gl = s_seq il in
    let tl = G.index gl t in
    T.evict_seq ep tl

#push-options "--fuel 0 --ifuel 1 --query_stats"

let t_evict_i2g (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (t:nat{t < n})
  (i:SA.seq_index (t_evict_seq_il ep il t))
  : j:SA.seq_index (t_evict_seq_gl ep il t){S.index (t_evict_seq_il ep il t) i = S.index (t_evict_seq_gl ep il t) j}
  = let ta_il = t_evict_seq_il ep il t in
    let ta_gl = t_evict_seq_gl ep il t in
    let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec #n ep) (blum_evict_elem_src_ifn #vspec #n) in
    let a_il = evict_il ep il in
    let gl = to_glog il in
    let tl = G.index gl t in

    (* index in the evict seq sequence *)
    let i1 = s2i_map a_il (t,i) in
    assert(i2s_map a_il i1 = (t,i));
    assert(src a_il i1 = t);

    (* index in the interleaved sequence il *)
    let i2 = IF.filter_map_invmap fm il i1 in
    assert(blum_evict_elem il i2 = S.index ta_il i);
    assert(src il i2 = t);

    (* index in the original log of the t'th thread *)
    let _,i3 = i2s_map il i2 in
    assert(T.blum_evict_elem tl i3 = blum_evict_elem il i2);

    (* map i3 to the evict seq - the index with ta_gl *)
    T.evict_seq_map tl i3

let t_evict_i2g_mono (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (t:nat{t < n})
  : Lemma (ensures (monotonic_prop (t_evict_i2g ep il t)))
          [SMTPat (t_evict_i2g ep il t)]
  = let ta_il = t_evict_seq_il ep il t in
    let ta_gl = t_evict_seq_gl ep il t in
    let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec #n ep) (blum_evict_elem_src_ifn #vspec #n) in
    let a_il = evict_il ep il in
    let gl = to_glog il in
    let tl = G.index gl t in

    let f = t_evict_i2g ep il t in

    let aux (i j: SA.seq_index ta_il)
      : Lemma (ensures (i < j ==> f i < f j))
      = if i < j then (
          let i1 = s2i_map a_il (t,i) in
          let j1 = s2i_map a_il (t,j) in
          s2i_map_monotonic a_il (t,i) (t,j);
          assert(i1 < j1);

          let i2 = IF.filter_map_invmap fm il i1 in
          let j2 = IF.filter_map_invmap fm il j1 in
          IF.filter_map_invmap_monotonic fm il i1 j1;
          assert(i2 < j2);

          let _,i3 = i2s_map il i2 in
          let _,j3 = i2s_map il j2 in
          i2s_map_monotonic il i2 j2;
          assert(i3 < j3);

          T.evict_seq_map_monotonic tl i3 j3
        )
    in
    forall_intro_2 aux

let t_evict_g2i (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (t:nat{t < n})
  (j:SA.seq_index (t_evict_seq_gl ep il t))
  : i:SA.seq_index (t_evict_seq_il ep il t){S.index (t_evict_seq_il ep il t) i = S.index (t_evict_seq_gl ep il t) j}
  = let ta_il = t_evict_seq_il ep il t in
    let ta_gl = t_evict_seq_gl ep il t in
    let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec #n ep) (blum_evict_elem_src_ifn #vspec #n) in
    let a_il = evict_il ep il in
    let gl = to_glog il in
    let tl = G.index gl t in

    let j1 = T.evict_seq_invmap ep tl j in
    let j2 = s2i_map il (t,j1) in
    assert(is_blum_evict il j2);
    assert(blum_evict_elem il j2 = T.blum_evict_elem tl j1);
    let j3 = IF.filter_map_map fm il j2 in
    let _,j4 = i2s_map a_il j3 in
    j4

let t_evict_g2i_mono (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (t:nat{t < n})
  : Lemma (ensures (monotonic_prop (t_evict_g2i ep il t)))
  = let ta_il = t_evict_seq_il ep il t in
    let ta_gl = t_evict_seq_gl ep il t in
    let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec #n ep) (blum_evict_elem_src_ifn #vspec #n) in
    let a_il = evict_il ep il in
    let gl = to_glog il in
    let tl = G.index gl t in

    let f = t_evict_g2i ep il t in
    let aux (i j: SA.seq_index ta_gl)
      : Lemma (ensures (i < j ==> f i < f j))
      = if i < j then (
          let i1 = T.evict_seq_invmap ep tl i in
          let j1 = T.evict_seq_invmap ep tl j in
          T.evict_seq_invmap_monotonic ep tl i j;
          assert(i1 < j1);

          let i2 = s2i_map il (t,i1) in
          let j2 = s2i_map il (t,j1) in
          s2i_map_monotonic il (t,i1) (t,j1);
          assert(i2 < j2);

          let i3 = IF.filter_map_map fm il i2 in
          let j3 = IF.filter_map_map fm il j2 in
          IF.lemma_filter_map_map_monotonic fm il i2 j2;
          assert(i3 < j3);

          i2s_map_monotonic a_il i3 j3
        )
    in
    forall_intro_2 aux

#pop-options

#push-options "--z3rlimit_factor 3"

let evict_seq_identical_thread (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (t: nat{t < n})
  : Lemma (ensures (t_evict_seq_il ep il t == t_evict_seq_gl ep il t))
   = monotonic_bijection_implies_equal
      (t_evict_seq_il ep il t)
      (t_evict_seq_gl ep il t)
      (t_evict_i2g ep il t)
      (t_evict_g2i ep il t)

#pop-options

#push-options "--fuel 0 --ifuel 1 --query_stats"

let evict_sseq_identical (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : Lemma (ensures (s_seq (evict_il ep il) == G.evict_sseq ep (to_glog il)))
  = let a_il = evict_il ep il in
    let a_ss1 = s_seq a_il in
    let gl = to_glog il in
    let a_ss2 = G.evict_sseq ep gl in

    let aux (t:_)
      : Lemma (ensures (S.index a_ss1 t == S.index a_ss2 t))
      = evict_seq_identical_thread ep il t
    in
    forall_intro aux;
    assert(S.equal a_ss1 a_ss2)

let evict_set_identical (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : Lemma (ensures (evict_set ep il == G.evict_set ep (to_glog il)))
  = evict_sseq_identical ep il;
    Zeta.MultiSet.SSeq.lemma_interleaving_multiset #_ #(ms_hashfn_dom_cmp vspec.app) (evict_il ep il)

#pop-options

let lemma_add_evict_ep_i2g (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : Lemma (requires (add_set ep il == evict_set ep il))
          (ensures (let gl = to_glog il in
                    G.add_set ep gl == G.evict_set ep gl))
  = add_set_identical ep il;
    evict_set_identical ep il

let lemma_add_evict_ep_g2i (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : Lemma (requires (let gl = to_glog il in
                     G.add_set ep gl == G.evict_set ep gl))
          (ensures (add_set ep il == evict_set ep il))
  = add_set_identical ep il;
    evict_set_identical ep il

let lemma_add_evict_set_dir1 (#vspec #n:_) (epmax: epoch) (il: verifiable_log vspec n)
  : Lemma (requires (aems_equal_upto epmax il))
          (ensures (G.aems_equal_upto epmax (to_glog il)))
  = let gl = to_glog il in
    let aux (ep:epoch)
      : Lemma (ensures (ep <= epmax ==> G.add_set ep gl == G.evict_set ep gl))
      = if ep <= epmax then
          lemma_add_evict_ep_i2g ep il
    in
    forall_intro aux

let lemma_add_evict_set_dir2 (#vspec #n:_) (epmax: epoch) (il: verifiable_log vspec n)
  : Lemma (requires (G.aems_equal_upto epmax (to_glog il)))
          (ensures (aems_equal_upto epmax il))

  = let gl = to_glog il in
    let aux (ep:epoch)
      : Lemma (ensures (ep <= epmax ==> add_set ep il == evict_set ep il))
      = if ep <= epmax then
          lemma_add_evict_ep_g2i ep il
    in
    forall_intro aux

let lemma_add_evict_set_identical_glog (#vspec #n:_) (epmax: epoch) (il: verifiable_log vspec n)
  : Lemma (ensures (aems_equal_upto epmax il <==> G.aems_equal_upto epmax (to_glog il)))
  = introduce aems_equal_upto epmax il ==> G.aems_equal_upto epmax (to_glog il)
    with _. lemma_add_evict_set_dir1 epmax il;
    introduce G.aems_equal_upto epmax (to_glog il) ==> aems_equal_upto epmax il
    with _. lemma_add_evict_set_dir2 epmax il

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

let rec index_mem_2 (#a:eqtype) (s: S.seq a) (x: a {S.count x s >= 2})
  : Tot (ij:(SA.seq_index s * SA.seq_index s)
         {let i,j = ij in
          i <> j /\ S.index s i = x /\ S.index s j = x})
    (decreases S.length s)
  = assert(S.length s > 0);
    if S.head s = x then
      (0, 1 + (S.index_mem  x (S.tail s)))
    else
      let i,j = index_mem_2 (S.tail s) x in
      (i + 1, j + 1)

#push-options "--fuel 0 --ifuel 1 --query_stats"

let evict_elems_distinct (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  (i1 i2: SA.seq_index (evict_seq ep il))
  : Lemma (ensures (let es = evict_seq ep il in
                    i1 <> i2 ==> S.index es i1 <> S.index es i2))
  = let evil = evict_il ep il in
    let gl = to_glog il in
    let t1 = src evil i1 in
    let tl1 = G.index gl t1 in
    let _,j1 = i2s_map evil i1 in
    let t2 = src evil i2 in
    let tl2 = G.index gl t2 in
    let _,j2 = i2s_map evil i2 in
    evict_seq_identical_thread ep il t1;
    evict_seq_identical_thread ep il t2;

    if i1 <> i2 then (
      if t1 <> t2 then (
        T.evict_elem_tid ep tl1 j1;
        T.evict_elem_tid ep tl2 j2
      )
      else (
        i2s_map_monotonic evil i1 i2;
        assert(j1 <> j2);
        T.evict_elem_unique ep tl1 j1 j2
      )
    )

let evict_mem_atmost_one (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (be: ms_hashfn_dom vspec.app)
  : Lemma (ensures (mem be (evict_set ep il) <= 1))
  = let esq = evict_seq ep il in
    let es = evict_set ep il in
    seq2mset_mem #_ #(ms_hashfn_dom_cmp vspec.app) esq be;
    if mem be es >= 2 then
      let i,j = index_mem_2 esq be in
      evict_elems_distinct ep il i j

#pop-options

let evict_set_is_a_set (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : Lemma (ensures (is_set (evict_set ep il)) )
  = forall_intro (evict_mem_atmost_one ep il)

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
 = let be = blum_add_elem itsl i in
   let ep = be.t.e in
   let es = evict_set ep itsl in

   if es `contains` be then
     let j = evict_elem_idx itsl be in
     eliminate forall (i j: seq_index itsl). i <= j ==> clock itsl i `ts_leq` clock itsl j with i j

(* the add seq of a prefix is the prefix of the evict sequence *)
let prefix_add_commute
  (#vspec #n:_)
  (ep: epoch)
  (il: verifiable_log vspec n)
  (l: nat{ l <= length il })
  : Lemma (ensures (let il' = prefix il l in
                    let as = add_seq ep il in
                    let as' = add_seq ep il' in
                    as' `SA.prefix_of` as))
  = let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec #n ep) (blum_add_elem_src_ifn #vspec #n) in
    let il' = prefix il l in
    let ail = add_il ep il in
    let as = add_seq ep il in
    let as' = add_seq ep il' in
    let ail' = add_il ep il' in
    IF.lemma_filter_map_prefix fm il l;
    assert(ail' `SA.prefix_of` ail);
    lemma_iseq_prefix_property ail (S.length ail')

(* the evict seq of a prefix is the prefix of the evict sequence *)
let prefix_evict_commute
  (#vspec #n:_)
  (ep: epoch)
  (il: verifiable_log vspec n)
  (l: nat{ l <= length il })
  : Lemma (ensures (let il' = prefix il l in
                    let es = evict_seq ep il in
                    let es' = evict_seq ep il' in
                    es' `SA.prefix_of` es))
  = let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec #n ep) (blum_evict_elem_src_ifn #vspec #n) in
    let il' = prefix il l in
    let evil = evict_il ep il in
    let es = evict_seq ep il in
    let es' = evict_seq ep il' in
    let evil' = evict_il ep il' in
    IF.lemma_filter_map_prefix fm il l;
    assert(evil' `SA.prefix_of` evil);
    lemma_iseq_prefix_property evil (S.length evil')

(* if an add set contains an element, then the epoch of the blum element is that of the add set*)
let lemma_add_set_only_epoch
  (#vspec #n:_)
  (ep: epoch)
  (il: verifiable_log vspec n)
  (be: ms_hashfn_dom vspec.app)
  : Lemma (ensures (let as = add_set ep il in
                    as `contains` be ==> be.t.e = ep))
  = let as = add_set ep il in
    let asq = add_seq ep il in
    let ail = add_il ep il in
    let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec #n ep) (blum_add_elem_src_ifn #vspec #n) in

    if as `contains` be then (
      seq2mset_mem #_ #(ms_hashfn_dom_cmp vspec.app) asq be;
      let j = S.index_mem be asq in
      index_prop ail j
    )

(* a slightly different version of of the previous lemma - the count of an add element
 * in the evict set is the same in the prefix as the full sequence *)
let lemma_evict_before_add2
  (#vspec #n:_)
  (ep: epoch)
  (itsl: its_log vspec n)
  (l:nat{l <= length itsl})
  (be: ms_hashfn_dom vspec.app)
  : Lemma (requires (let itsli = prefix itsl l in
                     let as = add_set ep itsli in
                     let es = evict_set ep itsli in
                     mem be as > mem be es))
          (ensures (let as = add_set ep itsl in
                    let es = evict_set ep itsl in
                    mem be as > mem be es))
  = let itsl' = prefix itsl l in
    let as = add_set ep itsl in
    let asq = add_seq ep itsl in
    let as' = add_set ep itsl' in
    let asq' = add_seq ep itsl' in
    let es = evict_set ep itsl in
    let es' = evict_set ep itsl' in
    let fma = IF.to_fm (is_blum_add_epoch_ifn #vspec #n ep) (blum_add_elem_src_ifn #vspec #n) in

    assert(as' `contains` be);
    lemma_add_set_only_epoch ep itsl' be;
    assert(be.t.e = ep);

    prefix_add_commute ep itsl l;
    assert(asq' `SA.prefix_of` asq);
    seq_prefix_mset_mem #_ #(ms_hashfn_dom_cmp vspec.app) asq asq' be;

    let i = some_add_elem_idx itsl' be in
    assert(blum_add_elem itsl i = be);

    if es `contains` be then (
      lemma_evict_before_add itsl i;
      let j = evict_elem_idx itsl be in
      assert(j < i);
      evict_set_contains_each_evict_elem itsl' j;
      assert(es' `contains` be);
      assert(mem be as' >= 2);

      evict_mem_atmost_one ep itsl be;
      assert(mem be es <= 1);

      ()
    )

let lemma_add_set_mem (#vspec #n:_) (il: verifiable_log vspec n) (i1 i2: seq_index il)
  : Lemma (requires (i1 <> i2 /\ is_blum_add il i1 /\ is_blum_add il i2 /\
                     blum_add_elem il i1 = blum_add_elem il i2))
          (ensures (let be = blum_add_elem il i1 in
                    let ep = be.t.e in
                    mem be (add_set ep il) >= 2))
  = let be = blum_add_elem il i1 in
    let ep = be.t.e in
    let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec #n ep) (blum_add_elem_src_ifn #vspec #n) in
    let ail = add_il ep il in
    let asq = add_seq ep il in

    let j1 = IF.filter_map_map fm il i1 in
    let j2 = IF.filter_map_map fm il i2 in
    IF.lemma_filter_map_map_monotonic fm il i1 i2;
    assert(j1 <> j2);

    index_prop ail j1;
    index_prop ail j2;
    seq_mset_elem2 #_ #(ms_hashfn_dom_cmp vspec.app) asq j1 j2

let is_blum_add_of_key_ifn (#vspec: verifier_spec) (#n:_) (ep: epoch) (gk: key vspec.app)
  : IF.idxfn_t (gen_seq vspec n) bool
  = is_blum_add_of_key #vspec #n ep gk

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

let k_add_set_correct
  (#vspec: verifier_spec)
  (#n:_)
  (ep: epoch)
  (gk: key vspec.app)
  (il: verifiable_log vspec n {length il > 0})
  (be: ms_hashfn_dom vspec.app)
  : Lemma (ensures (let gkc,_ = be.r in
                    k_add_set ep gk il `contains` be ==> gkc = gk /\ be.t.e = ep))
  = let kas = k_add_set ep gk il in
    let kasq = k_add_seq ep gk il in
    let kail = k_add_il ep gk il in
    let fm = IF.to_fm (is_blum_add_of_key_ifn #vspec #n ep gk) (blum_add_elem_src_ifn #vspec #n) in

    if kas `contains` be then (
      seq2mset_mem #_ #(ms_hashfn_dom_cmp vspec.app) kasq be;
      let j = S.index_mem be kasq in
      index_prop kail j
    )

let k_evict_set_correct
  (#vspec: verifier_spec)
  (#n:_)
  (ep: epoch)
  (gk: key vspec.app)
  (il: verifiable_log vspec n {length il > 0})
  (be: ms_hashfn_dom vspec.app)
  : Lemma (ensures (let gkc,_ = be.r in
                    k_evict_set ep gk il `contains` be ==> gkc = gk /\ be.t.e = ep))
  = let kes = k_evict_set ep gk il in
    let kesq = k_evict_seq ep gk il in
    let keil = k_evict_il ep gk il in
    let fm = IF.to_fm (is_blum_add_of_key_ifn #vspec #n ep gk) (blum_add_elem_src_ifn #vspec #n) in

    if kes `contains` be then (
      seq2mset_mem #_ #(ms_hashfn_dom_cmp vspec.app) kesq be;
      let j = S.index_mem be kesq in
      index_prop keil j
    )

let k_add_set_empty
  (#vspec: verifier_spec)
  (#n:_)
  (ep: epoch)
  (gk: key vspec.app)
  (il: verifiable_log vspec n {length il = 0})
  : Lemma (ensures (k_add_set ep gk il == empty))
  = zero_length_implies_empty #_ #(ms_hashfn_dom_cmp vspec.app) (k_add_seq ep gk il)

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
  = let fm = IF.to_fm (is_blum_add_of_key_ifn #vspec #n ep gk) (blum_add_elem_src_ifn #vspec #n) in
    IF.lemma_filter_map_snoc fm il;
    let i = length il - 1 in
    if is_blum_add_of_key ep gk il i then (
      admit()
    )

let k_evict_set_empty
  (#vspec: verifier_spec)
  (#n:_)
  (ep: epoch)
  (gk: key vspec.app)
  (il: verifiable_log vspec n {length il = 0})
  : Lemma (ensures (k_evict_set ep gk il == empty))
  = zero_length_implies_empty #_ #(ms_hashfn_dom_cmp vspec.app) (k_evict_seq ep gk il)

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
