module Veritas.SeqAux

open FStar.Seq

(* Legitimate values of an index of a sequence *)
inline_for_extraction
type seq_index (#a:Type) (s:seq a) = i:nat{i < length s}

(* Prefix of a sequence *)
val prefix (#a:Type) (s:seq a) (i:nat{i <= length s}): Tot (s':seq a{length s' = i})

(* append a single element to the end of a sequence *)
let append1 (#a:Type) (s:seq a) (x:a): s':(seq a){length s' = length s + 1} =
  append s (create 1 x)

val lemma_prefix_index (#a:Type) (s:seq a) (i:nat{i <= length s}) (j:nat{j < i}):
  Lemma (requires (True))
        (ensures (index (prefix s i) j == index s j))
        [SMTPat (index (prefix s i) j)]

val lemma_prefix_prefix (#a:Type) (s:seq a) (i:nat{i <= length s}) (j:nat{j <= i}):
  Lemma (requires (True))
        (ensures (prefix (prefix s i) j == prefix s j))
        [SMTPat (prefix (prefix s i) j)]

val lemma_fullprefix_equal (#a:Type) (s:seq a):
  Lemma (requires (True))
        (ensures (prefix s (length s) == s))
        [SMTPat (prefix s (length s))]

val lemma_prefix_append (#a:Type) (s1 s2: seq a):
  Lemma (requires (True))
        (ensures (prefix (append s1 s2) (length s1) == s1))

val lemma_prefix0_empty (#a:Type) (s: seq a):
  Lemma (prefix s 0 == empty #a)

(* is ps a prefix of s *)
let is_prefix (#a:eqtype) (s:seq a) (ps: seq a): Tot bool =
  length ps <= length s &&
  ps = prefix s (length ps)

(* Suffix of a sequence *)
val suffix (#a:Type) (s:seq a) (i:nat{i <= length s}): Tot (s':seq a{length s' = i})

val lemma_suffix_index (#a:Type) (s:seq a) (i:nat{i <= length s}) (j:nat{j < i}):
  Lemma (requires (True))
        (ensures (index (suffix s i) j == index s (length s - i + j)))
        [SMTPat (index (suffix s i) j)]

(* projection - a subsequence of the original sequence *)
val proj (#a:eqtype): seq a -> seq a -> Type0

(* mapping from a subsequence index to the corresponding index in the base sequence *)
val proj_index_map (#a:eqtype) (ss: seq a) (s: seq a) (prf: proj ss s) (i:seq_index ss):
  Tot (j:seq_index s{index s j = index ss i})

(* the mapping we construct above is monotonic *)
val lemma_proj_monotonic (#a:eqtype) (ss s: seq a) (prf: proj ss s) (i1 i2: seq_index ss):
  Lemma (requires (i1 < i2))
        (ensures (proj_index_map ss s prf i1 < proj_index_map ss s prf i2))

val lemma_proj_length (#a:eqtype) (ss: seq a) (s:seq a{proj ss s}):
  Lemma (requires (True))
        (ensures (length ss <= length s))

(* subsequence of s obtained by applying a filter *)
val filter (#a:eqtype) (f:a -> bool) (s:seq a): Tot (seq a)

(* filter is a projection *)
val lemma_filter_is_proj (#a:eqtype) (f:a -> bool) (s:seq a):
  Lemma (proj (filter f s) s)

(* constructive version of the lemma_filter_is_proj *)
val filter_is_proj_prf (#a:eqtype) (f:a -> bool) (s:seq a): Tot (proj (filter f s) s)

(* every index in the filtered sequence satisfies the filter predicate *)
val lemma_filter_correct1 (#a: eqtype) (f:a -> bool) (s:seq a) (i:seq_index (filter f s)):
  Lemma (requires (True))
        (ensures (f (index (filter f s) i) = true))
        [SMTPat (f (index (filter f s) i))]

val lemma_filter_correct_all (#a:eqtype) (f:a -> bool) (s:seq a):
  Lemma (requires (True))
        (ensures (forall (i:(seq_index (filter f s))). f (index (filter f s) i) = true))

(* mapping from filtered subseq to satisfying indexes *)
val filter_index_map (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index (filter f s)):
  Tot (j:seq_index s{index s j = index (filter f s) i})

(* Mapping from original seq to filtered subseq for satisfying indexes *)
val filter_index_inv_map (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index s{f (index s i)}):
  Tot (j:seq_index (filter f s){index s i = index (filter f s) j})

inline_for_extraction
let refine #a (f:a -> bool) = x:a{f x}

type all (#a:Type) (f:a -> bool) (s: seq a) =
  forall (i:seq_index s). f (index s i)

(* if we know that every element of a seq satisfies f, then the same sequence is a sequence over
 * the refinement defined by f *)
val seq_refine (#a:Type) (f:a -> bool) (s:seq a{all f s}): Tot (seq (refine f))

val lemma_seq_refine_len (#a:Type) (f:a->bool) (s:seq a{all f s}):
  Lemma (requires True)
        (ensures (length (seq_refine f s) = length s))
        [SMTPat (seq_refine f s)]

val lemma_seq_refine_equal (#a:Type) (f:a->bool) (s:seq a{all f s}) (i:seq_index s):
  Lemma (requires True)
        (ensures (index (seq_refine f s) i == index s i))
        [SMTPat (index (seq_refine f s) i)]

let filter_refine (#a:eqtype) (f:a -> bool) (s: seq a): Tot (seq (refine f)) =
  let fs = filter f s in
  seq_refine f fs

(* filter_index_map is injective *)
val lemma_filter_index_map_monotonic (#a:eqtype) (f:a -> bool) (s:seq a)
  (i:seq_index (filter f s))(j:seq_index (filter f s){j > i}):
  Lemma (filter_index_map f s i < filter_index_map f s j)

(* Inverse mapping is injective *)
val lemma_filter_index_inv_map_monotonic (#a:eqtype) (f:a -> bool) (s: seq a)
  (i:seq_index s) (j: seq_index s {j > i}):
    Lemma (requires (f (index s i) /\ f (index s j)))
          (ensures (filter_index_inv_map f s i < filter_index_inv_map f s j))

val lemma_filter_maps_correct (#a:eqtype) (f:a -> bool) (s: seq a) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (filter_index_map f s (filter_index_inv_map f s i) = i))

val lemma_filter_maps_correct2 (#a:eqtype) (f:a -> bool) (s: seq a) (i: seq_index (filter f s)):
  Lemma (requires(True))
        (ensures (filter_index_inv_map f s (filter_index_map f s i) = i))
        [SMTPat (filter_index_map f s i)]

val lemma_filter_empty (#a:eqtype) (f:a -> bool):
  Lemma (filter f (empty #a) == empty #a)

val lemma_filter_prefix (#a:eqtype) (f:a -> bool) (s: seq a) (ps: seq a{is_prefix s ps}):
  Lemma (is_prefix (filter f s) (filter f ps))

val lemma_filter_prefix_comm (#a:eqtype) (f:a->bool) (s: seq a) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (filter f (prefix s i) = prefix (filter f s) (filter_index_inv_map f s i)))

val lemma_filter_extend1 (#a:eqtype) (f:a -> bool) (s:seq a{length s > 0}):
  Lemma (requires (not (f (index s (length s - 1)))))
        (ensures (filter f s = filter f (prefix s (length s - 1))))

val lemma_filter_extend2 (#a:eqtype) (f:a -> bool) (s:seq a{length s > 0}):
  Lemma (requires (f (index s (length s - 1))))
        (ensures (filter f s = append1 (filter f (prefix s (length s - 1))) (index s (length s - 1))))

let ext_pred (#a:eqtype) (f1 f2:a -> bool) =
  forall x. f1 x = f2 x

val lemma_filter_extensionality (#a:eqtype) (f1 f2:a -> bool) (s:seq a):
  Lemma (requires (ext_pred f1 f2))
        (ensures (filter f1 s = filter f2 s))

let conj (#a:eqtype) (f1 f2: a -> bool) (x: a) =
  f1 x && f2 x

val lemma_filter_conj (#a:eqtype) (f1 f2: a -> bool) (s:seq a):
  Lemma (filter (conj f1 f2) s = filter f1 (filter f2 s))

val lemma_filter_comm (#a:eqtype) (f1 f2:a -> bool) (s:seq a):
  Lemma (filter f2 (filter f1 s) = filter f1 (filter f2 s))

(* The index of the last entry that satisfies a given property *)
val last_index_opt (#a:eqtype) (f:a -> bool) (s:seq a):
  Tot (option (i:seq_index s{f (index s i)}))

(* There exists some element satisfying f if there exists last_index *)
let exists_sat_elems (#a:eqtype) (f:a -> bool) (s:seq a) =
  Some? (last_index_opt f s)

(* The index of the last entry when we know there exists such entry *)
let last_index (#a:eqtype) (f:a -> bool) (s:seq a{exists_sat_elems f s}) =
  Some?.v (last_index_opt f s)

(* Any index beyond last index does not satisfy f *)
val lemma_last_index_correct1 (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index s):
  Lemma (requires (exists_sat_elems f s /\ i > last_index f s))
        (ensures (not (f (index s i))))

(* Any witness satisfying f implies last_index exists *)
val lemma_last_index_correct2 (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (exists_sat_elems f s /\ last_index f s >= i))

(* Taking the prefix of a sequence upto last_index does not alter last_index *)
val lemma_last_index_prefix (#a:eqtype) (f:a -> bool) (s:seq a) (i:nat{i <= length s}):
  Lemma (requires (exists_sat_elems f s /\ i > last_index f s))
        (ensures (exists_sat_elems f (prefix s i) /\
                  last_index f s = last_index f (prefix s i)))

(* If s does not have elements satisfying f then no prefix of s has as well *)
val lemma_not_exists_prefix (#a:eqtype) (f:a -> bool) (s:seq a) (i:nat{i <= length s}):
  Lemma (requires (not (exists_sat_elems f s)))
        (ensures (not (exists_sat_elems f (prefix s i))))

val lemma_exists_prefix_implies_exists (#a:eqtype) (f:a -> bool) (s:seq a) (i:nat{i <= length s}):
  Lemma (requires (exists_sat_elems f (prefix s i)))
        (ensures (exists_sat_elems f s))
        [SMTPat (exists_sat_elems f (prefix s i))]

val lemma_last_index_last_elem_nsat (#a:eqtype) (f:a -> bool) (s:seq a{length s > 0}):
  Lemma (requires (not (f (index s (length s - 1)))))
        (ensures ((exists_sat_elems f s ==> last_index f s < length s - 1) /\
                  exists_sat_elems f s = exists_sat_elems f (prefix s (length s - 1))))

val lemma_last_index_last_elem_sat (#a:eqtype) (f:a -> bool) (s:seq a{length s > 0}):
  Lemma (requires (f (index s (length s - 1))))
        (ensures (exists_sat_elems f s /\ last_index f s = length s - 1))

val lemma_exists_sat_elems_extensionality (#a:eqtype) (f1 f2:a -> bool) (s: seq a):
  Lemma (requires (ext_pred f1 f2))
        (ensures (exists_sat_elems f1 s = exists_sat_elems f2 s))

val lemma_last_index_extensionality (#a:eqtype) (f1 f2:a -> bool) (s: seq a{exists_sat_elems f1 s}):
  Lemma (requires (ext_pred f1 f2))
        (ensures (exists_sat_elems f2 s /\
                  last_index f1 s = last_index f2 s))

val lemma_exists_sat_conj (#a:eqtype) (f1 f2: a -> bool) (s: seq a):
  Lemma(requires True)
       (ensures (exists_sat_elems (conj f1 f2) s = exists_sat_elems f1 (filter f2 s)))
       [SMTPat (exists_sat_elems (conj f1 f2) s)]

val lemma_last_idx_conj (#a:eqtype) (f1 f2: a -> bool)
                        (s: seq a{exists_sat_elems (conj f1 f2) s}):
  Lemma (last_index (conj f1 f2) s = filter_index_map f2 s (last_index f1 (filter f2 s)))

(* The index of the first entry that satisfies a given property *)
val first_index (#a:eqtype) (f:a -> bool) (s:seq a{exists_sat_elems f s})
  : Tot (i:seq_index s{f (index s i)})

(* Any index before first index does not satisfy f *)
val lemma_first_index_correct1 (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index s):
  Lemma (requires (exists_sat_elems f s /\ i < first_index f s))
        (ensures (not (f (index s i))))

(* Any witness satisfying f implies first_index exists *)
val lemma_first_index_correct2 (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (exists_sat_elems f s /\ first_index f s <= i))

(* Map every element of a sequence to another domain to get another sequence *)
val map (#a #b:Type) (f:a -> b) (s:seq a): Tot (s':seq b{length s' = length s})

val lemma_map_index (#a #b: Type) (f:a -> b) (s:seq a) (i:seq_index s):
  Lemma (requires (True))
        (ensures (f (index s i) == index (map f s) i))
        [SMTPat (index (map f s) i)]

val lemma_map_prefix (#a #b: Type) (f:a -> b) (s:seq a) (i: seq_index s):
  Lemma (requires True)
        (ensures (map f (prefix s i) == prefix (map f s) i))

val zip (#a #b: eqtype) (sa: seq a) (sb: seq b{length sb = length sa}):
  sab: seq (a * b){length sab = length sa}

val lemma_zip_index (#a #b: eqtype) (sa: seq a) (sb: seq b{length sb = length sa}) (i: seq_index sa):
  Lemma (requires (True))
        (ensures (fst (index (zip sa sb) i) = index sa i /\
                  snd (index (zip sa sb) i) = index sb i))
        [SMTPat (index (zip sa sb) i)]

val unzip (#a #b: eqtype) (sab: seq (a * b)): sasb: (seq a * seq b)
  {length (fst sasb) = length sab /\
   length (snd sasb) = length sab}

val lemma_unzip_index (#a #b: eqtype) (sab: seq (a * b)) (i:seq_index sab):
  Lemma (requires (True))
        (ensures (fst (index sab i) = index (fst (unzip sab)) i /\
                  snd (index sab i) = index (snd (unzip sab)) i))
        [SMTPat (index (fst (unzip sab)) i); SMTPat (index (snd (unzip sab)) i)]

val lemma_zip_unzip (#a #b: eqtype) (sa: seq a) (sb: seq b{length sb = length sa}):
  Lemma (requires (True))
        (ensures ((sa, sb) = unzip (zip sa sb)))

(* attach their index to elements of a sequence *)
val attach_index (#a:Type) (s:seq a): Tot (seq (nat * a))

val lemma_attach_len (#a:Type) (s: seq a):
  Lemma (requires (True))
        (ensures (length (attach_index s) = length s))
        [SMTPat (attach_index s)]

val lemma_attach_correct (#a:Type) (s:seq a) (i: seq_index s):
  Lemma (requires (True))
        (ensures (length (attach_index s) = length s /\
                  snd (index (attach_index s) i) == index s i /\
                  fst (index (attach_index s) i) = i))
        [SMTPat (index (attach_index s) i)]

(* reduce operation over sequences *)
val reduce (#a:Type) (#b:Type) (b0: b) (f: a -> b -> b) (s: seq a): Tot b

val lemma_reduce_empty (#a:Type) (#b:eqtype) (b0:b) (f:a -> b -> b):
  Lemma (reduce b0 f (empty #a) = b0)

val lemma_reduce_prefix (#a:Type) (#b:eqtype) (b0: b) (f: a -> b -> b) (s: seq a) (i:nat{i <= length s}):
  Lemma (reduce b0 f s = reduce (reduce b0 f (prefix s i)) f (suffix s (length s - i)))

val lemma_reduce_property_closure (#a:Type) (#b:eqtype) (p: b -> bool) (b0:b) (f: a -> b -> b) (s: seq a):
  Lemma (requires (p b0 /\ (forall (x:a). forall (y:b). (p y ==> p (f x y)))))
        (ensures (p (reduce b0 f s)))

val lemma_reduce_identity (#a:Type) (#b:eqtype) (b0: b) (f: a -> b -> b) (s: seq a):
  Lemma (requires (forall (x:a). f x b0 = b0))
        (ensures (reduce b0 f s = b0))

val lemma_reduce_singleton (#a:Type) (#b:eqtype) (b0: b) (f: a -> b -> b) (s: seq a{length s = 1}):
  Lemma (reduce b0 f s = f (index s 0) b0)

val lemma_reduce_append (#a:Type) (#b:eqtype) (b0:b) (f: a -> b -> b) (s: seq a) (x:a):
  Lemma (reduce b0 f (append1 s x) = f x (reduce b0 f s))

val lemma_reduce_append2 (#a:Type) (#b:eqtype) (b0:b) (f: a -> b -> b) (s: seq a{length s > 0}):
  Lemma (reduce b0 f s = f (index s (length s - 1)) (reduce b0 f (prefix s (length s - 1))))

