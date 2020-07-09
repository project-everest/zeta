module Veritas.SeqAux

open FStar.Seq 

(* Legitimate values of an index of a sequence *)
inline_for_extraction
type seq_index (#a:Type) (s:seq a) = i:nat{i < length s}

(* Prefix of a sequence *)
val prefix (#a:Type) (s:seq a) (i:nat{i <= length s}): Tot (s':seq a{length s' = i})

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

(* if we know that every element of a seq satisfies f, then the same sequence is a sequence over 
 * the refinement defined by f *)
val seq_refine (#a:Type) (f:a -> bool) (s:seq a{forall (i:seq_index s). f (index s i)}): Tot (seq (refine f))

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
