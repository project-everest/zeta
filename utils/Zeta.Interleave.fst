module Zeta.Interleave

open FStar.Classical
open Zeta.SeqIdx

module IF = Zeta.IdxFn

let seq_index = SA.seq_index

let gen_seq (a:eqtype) (n:_) =
  {
    IF.a = elem_src a n;
    IF.phi = (fun _ -> True);
    IF.phi_commutes_with_prefix = (fun _ _ -> ());
  }

(* an element is from src t *)
let from_src #a #n (t: nat) (il: interleaving a n) (i: seq_index il)
  = t = (S.index il i).s

let to_elem #a #n (il: interleaving a n) (i: seq_index il)
  = (S.index il i).e

let i_seq (#a:_) (#n:nat) (il: interleaving a n)
  = IF.map #(gen_seq a n) (to_elem #a #n) il

let index_prop (#a #n:_) (il: interleaving a n) (i: SA.seq_index il)
  : Lemma (ensures ((S.index il i).e = index il i))
  = IF.lemma_map_map #(gen_seq a n) #_ to_elem il i

let seq_i_fm (a:eqtype) n (i:nat)
  : IF.fm_t (gen_seq a n) a
  = IF.FM (from_src #a #n i) (to_elem #a #n)

let s_seq_i (#a:_) (#n:_) (il: interleaving a n) (i:nat{i < n})
  = IF.filter_map (seq_i_fm a n i) il

let s_seq (#a:_) (#n:_) (il: interleaving a n)
  = init n (s_seq_i il)

let per_thread_prefix #a #n il i
  = let ss = s_seq il in
    let il' = prefix il i in
    let ss' = s_seq il' in
    let aux (t:_)
      : Lemma (ensures (S.index ss' t `prefix_of` S.index ss t))
      = IF.lemma_filter_map_prefix (seq_i_fm a n t) il i
    in
    forall_intro aux

let i2s_map (#a:_) (#n:_) (il:interleaving a n) (i:seq_index il)
  = let t = src il i in
    let fm = seq_i_fm a n t in
    let j = IF.filter_map_map fm il i in
    IF.lemma_map_map #(gen_seq a n) (to_elem #a #n) il i;
    (t,j)

let i2s_map_monotonic (#a #n:_) (il: interleaving a n) (i j: SA.seq_index il)
  : Lemma (requires (src il i = src il j))
          (ensures ((i < j ==> snd (i2s_map il i) < snd (i2s_map il j)) /\
                    (j < i ==> snd (i2s_map il j) < snd (i2s_map il i))))
  = let t = src il i in
    let fm = seq_i_fm a n t in
    IF.lemma_filter_map_map_monotonic fm il i j

let s2i_map (#a:_) (#n:_) (il:interleaving a n) (si: sseq_index (s_seq il))
  = let t,j = si in
    let fm = seq_i_fm a n t in
    let i = IF.filter_map_invmap fm il j in
    IF.lemma_map_map #(gen_seq a n) (to_elem #a #n) il i;
    i

let s2i_map_monotonic (#a #n:_) (il: interleaving a n) (i j: sseq_index (s_seq il))
  : Lemma (requires (fst i = fst j))
          (ensures ((snd i < snd j ==> s2i_map il i < s2i_map il j) /\
                    (snd j < snd i ==> s2i_map il j < s2i_map il i)))
  = let t = fst i in
    let fm = seq_i_fm a n t in
    IF.filter_map_invmap_monotonic fm il (snd i) (snd j)

let lemma_i2s_s2i (#a:_) (#n:_) (il:interleaving a n) (i:seq_index il):
  Lemma (ensures (s2i_map il (i2s_map il i) = i))
  = ()

let lemma_index_prefix_property (#a #n:_) (il:interleaving a n) (i:nat{i <= length il}) (j:nat{j < i}):
  Lemma (ensures (index (prefix il i) j = index il j))
  = IF.lemma_map_map #(gen_seq a n) (to_elem #a #n) il j;
    let fm = IF.map_fm #(gen_seq a n) #_ (to_elem #a #n)   in
    IF.filter_map_map_prefix_property fm il j i;
    ()

let lemma_prefix_prefix_property (#a #n:_) (il:interleaving a n) (i:nat{i <= length il}) (j:nat{j <= i}):
  Lemma (ensures (prefix (prefix il i) j == prefix il j))
  = ()

let lemma_iseq_prefix_property (#a:_) (#n:_) (il: interleaving a n) (i:nat{i <= length il})
  : Lemma (ensures (SA.prefix (i_seq il) i = i_seq (prefix il i)))
  = let fm = IF.map_fm #(gen_seq a n) #_ (to_elem #a #n)   in
    IF.lemma_filter_map_prefix fm il i

let lemma_i2s_prefix_property (#a:_) (#n:_) (il:interleaving a n)(i:nat{i <= length il})(j:nat{j < i}):
  Lemma (ensures (i2s_map (prefix il i) j = i2s_map il j))
  = let t = src il j in
    let fm = seq_i_fm a n t in
    IF.filter_map_map_prefix_property fm il j i;
    ()

let lemma_iseq_append1 (#a #n:_) (il': interleaving a n) (x: elem_src a n)
  : Lemma (ensures (let il = SA.append1 il' x in
                    i_seq il = SA.append1 (i_seq il') x.e))
  = let il = SA.append1 il' x in
    let fm = IF.map_fm #(gen_seq a n) #_ (to_elem #a #n)   in
    SA.lemma_prefix1_append il' x;
    IF.lemma_filter_map_snoc fm il

let lemma_length0_implies_empty (#a #n:_) (il: interleaving a n{length il = 0})
  : Lemma (ensures (il == empty_interleaving a n))
  = S.lemma_empty il

let lemma_empty_sseq (a:eqtype) (n:_) (i: nat{i < n})
  : Lemma (ensures (let il = empty_interleaving a n in
                    S.index (s_seq il) i = S.empty #a))
  = let il = empty_interleaving a n in
    S.lemma_empty (S.index (s_seq il) i)

#push-options "--fuel 1 --ifuel 1 --query_stats"

let i2s_map_snoc (#a #n:_) (il: interleaving a n{length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let t = src il i in
                    let ss = s_seq il in
                    let s = S.index ss t in
                    let sl = S.length s in
                    i2s_map il i = (t, sl - 1)))
  = let i = length il - 1 in
    let t = src il i in
    let ss = s_seq il in
    let s = S.index ss t in
    let sl = S.length s in

    let _,j = i2s_map il i in
    assert(sl > 0);
    if j < sl - 1 then
      let i' = s2i_map il (t,sl - 1) in
      s2i_map_monotonic il (t,j) (t,sl-1)

let interleaving_snoc (#a #n:_) (il: interleaving a n{length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let ss = s_seq il in
                    let is = i_seq il in
                    let il' = prefix il i in
                    let ss' = s_seq il' in
                    let is' = i_seq il' in
                    let x = index il i in
                    let t = src il i in
                    i2s_map il i = (t,S.length (S.index ss' t)) /\
                    ss' == sseq_prefix ss t /\
                    is' = SA.prefix is i))
  = let i = length il - 1 in
    let ss = s_seq il in
    let is = i_seq il in
    let t = src il i in
    let il' = prefix il i in
    let ss' = s_seq il' in
    let is' = i_seq il' in

    (* already proven in iseq_prefix_property *)
    assert(is' = SA.prefix is i);

    i2s_map_snoc il;

    let ss'2 = sseq_prefix ss t in
    let aux (tid:_)
      : Lemma (ensures (S.index ss' tid = S.index ss'2 tid))
      = let fm = seq_i_fm a n tid in
        IF.lemma_filter_map_snoc fm il;
        let s' = S.index ss' tid in
        if tid = t then
          lemma_prefix1_append s' (index il i)
    in
    forall_intro aux;
    assert(S.equal ss' ss'2);
    ()

#pop-options

let lemma_empty_interleaving_empty_sseq (a:eqtype) (n:nat)
  : Lemma (ensures (let il = empty_interleaving a n in
                    let ss = empty a n in
                    ss == s_seq il))
          [SMTPat (empty_interleaving a n)]
  = let il = empty_interleaving a n in
    let ss = empty a n in
    let ss2 = s_seq il in
    let aux(i:_)
      : Lemma (ensures (S.index ss i == S.index ss2 i))
      = lemma_empty_sseq a n i
    in
    forall_intro aux;
    assert(S.equal ss ss2)

let rec interleaving_flat_length (#a #n:_) (il: interleaving a n)
  : Lemma (ensures (flat_length (s_seq il) = length il))
          (decreases (length il))
  = let ss = s_seq il in
    if length il = 0 then (
      lemma_length0_implies_empty il;
      lemma_flat_length_emptyn a n
    )
    else (
      let i = length il - 1 in
      let t = src il i in
      let il' = prefix il i in
      interleaving_flat_length il';
      interleaving_snoc il;
      sseq_prefix_flatlen ss t
    )

#push-options "--z3rlimit_factor 3 --fuel 1 --ifuel 1 --query_stats"

let seq_equal_helper (#a:eqtype) (s1 s2: seq a)
  : Lemma (requires (let l1 = S.length s1 in
                     let l2 = S.length s2 in
                     l1 = l2 /\ l1 > 0 /\ SA.hprefix s1 = SA.hprefix s2 /\ SA.telem s1 = SA.telem s2))
          (ensures (s1 = s2))
   = let aux (i:_)
       : Lemma (ensures (S.index s1 i = S.index s2 i))
       = ()
    in
    forall_intro aux;
    assert(S.equal s1 s2)

let lemma_interleave_extend
  (#a:eqtype) (#n:_)
  (ss: sseq a{S.length ss = n})
  (t: nat{t < n})
  (il': interleaving a n)
  : Lemma (requires (S.length (S.index ss t) > 0 /\ s_seq il' == sseq_prefix ss t))
          (ensures (let s = S.index ss t in
                    let i = S.length s - 1 in
                    let e = S.index s i in
                    let il = SA.append1 il' ({e;s=t}) in
                    s_seq il == ss))
  = let s = S.index ss t in
    let i = length il' in
    let j = S.length s - 1 in
    let e = S.index s j in
    let il = SA.append1 il' ({e;s=t}) in
    lemma_prefix1_append il' ({e;s=t});
    assert(il' = prefix il i);
    interleaving_snoc il;
    let ss2 = s_seq il in
    let ss' = s_seq il' in
    assert(ss' == sseq_prefix ss t);
    assert(ss' == sseq_prefix ss2 t);

    let aux (tid:_)
      : Lemma (ensures (S.index ss tid = S.index ss2 tid))
      = let s2 = S.index ss2 tid in
        let l2 = S.length s2 in
        let l = S.length s in
        if tid = t then (
          assert(S.index ss' t = SA.prefix s2 (l2 - 1));
          assert(S.index ss' t = SA.prefix s (l - 1));
          assert(l2 = l);
          assert(S.index s (l-1) = e);
          assert(S.index s2 (l-1) = e);
          seq_equal_helper s s2
        )
        else (
          assert(S.index ss tid = S.index ss' tid);
          assert(S.index ss2 tid = S.index ss' tid);
          ()
        )
    in
    forall_intro aux;
    assert(S.equal ss ss2)

#pop-options

#push-options "--fuel 0 --ifuel 1 --query_stats"

let find_non_empty_seq (#a:_) (ss: sseq a {flat_length ss > 0})
  : i:SA.seq_index ss {S.length (S.index ss i) > 0}
  = nonzero_flatlen_implies_nonempty ss;
    let p = fun (s: seq a) -> S.length s > 0 in
    last_idx p ss

#pop-options

#push-options "--z3rlimit_factor 4"

let rec some_interleaving_alt (#a:eqtype) (ss: sseq a)
  : Tot(il: interleaving a (S.length ss) 
            {
              s_seq il = ss /\
              (forall (x:a). Seq.count x (i_seq il) == sum_count x ss)
            })
    (decreases (flat_length ss))
  = let m = flat_length ss in
    let n = S.length ss in
    if m = 0 then (
      (* if ss has flat length then it is empty *)
      lemma_flat_length_zero ss;
      assert(ss == empty _ n);
      let il = empty_interleaving a n in
      lemma_empty_interleaving_empty_sseq a n;
      FStar.Classical.forall_intro (sum_count_empty ss);
      il
    )
    else (
      let i = find_non_empty_seq ss in
      let s = S.index ss i in
      let sn = S.length s in

      let ss' = sseq_prefix ss i in
      let il' = some_interleaving_alt ss' in
      let e = S.index s (sn-1) in
      let il: interleaving a n = SA.append1 il' ({e; s = i}) in
      interleaving_snoc il;
      interleaving_flat_length il;
      lemma_prefix1_append il' ({e;s=i});
      lemma_interleave_extend ss i il';
      assert (forall (x:a). Seq.count x (i_seq il') == sum_count x ss');
      introduce forall (x:a). Seq.count x (i_seq il) == sum_count x ss
      with ( 
        calc (==) {
          sum_count x ss;
        (==) { sum_count_sseq_prefix ss i x }
          sum_count x ss' + (if x = Seq.last s then 1 else 0);
        (==) { }
          Seq.count x (i_seq il') + (if x = Seq.last s then 1 else 0);
        (==) { 
               assert (i_seq il `Seq.equal` Seq.snoc (i_seq il') e);
               SeqAux.count_snoc (i_seq il') e x 
             }
          Seq.count x (i_seq il);
        }
      );
      il
    )

#pop-options

let some_interleaving (#a:_) (ss: sseq a)
  : Tot(il: interleaving a (S.length ss) {s_seq il = ss})
  = some_interleaving_alt ss
  
let i_seq_count (#a: eqtype) (s: sseq a) (x:a)
  : Lemma 
    (ensures Seq.count x (i_seq (some_interleaving s)) == 
             Zeta.SSeq.sum_count x s)
  = ()
