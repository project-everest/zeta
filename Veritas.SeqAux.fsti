module Veritas.SeqAux

open FStar.Seq 

(* Legitimate values of an index of a sequence *)
type seq_index (#a:Type) (s:seq a) = i:nat{i < length s}

(* Prefix of a sequence *)
val prefix (#a:Type) (s:seq a) (i:nat{i <= length s}): Tot (s':seq a{length s' = i})

val lemma_prefix_index (#a:Type) (s:seq a) (i:nat{i <= length s}) (j:nat{j < i}):
  Lemma (requires (True))
        (ensures (index (prefix s i) j == index s j))

val lemma_prefix_prefix (#a:Type) (s:seq a) (i:nat{i <= length s}) (j:nat{j <= i}):
  Lemma (requires (True))
        (ensures (prefix (prefix s i) j == prefix s j))

(* Suffix of a sequence *)
val suffix (#a:Type) (s:seq a) (i:nat{i <= length s}): Tot (s':seq a{length s' = i})

val lemma_suffix_index (#a:Type) (s:seq a) (i:nat{i <= length s}) (j:nat{j < i}):
  Lemma (requires (True))
        (ensures (index (suffix s i) j == index s (length s - i + j)))

(* Subsequence of s obtained by applying a filter *)
val filter (#a:eqtype) (f:a -> bool) (s:seq a): Tot (seq a)

(* Mapping from original seq to filtered subseq for satisfying indexes *)
val filter_index_map (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index s{f (index s i)}):
  Tot (j:seq_index (filter f s){index s i = index (filter f s) j})

(* filter_index_map is injective *)
val filter_index_map_monotonic (#a:eqtype) (f:a -> bool) (s:seq a) 
  (i:seq_index s)(j:seq_index s{j > i}):
  Lemma (requires (f (index s i) && f (index s j)))
        (ensures (filter_index_map f s i < filter_index_map f s j))  

(* Inverse mapping from filtered subseq to satisfying indexes *)
val filter_index_inv_map (#a:eqtype) (f:a -> bool) (s:seq a) 
  (i:seq_index (filter f s)): 
  Tot (j:seq_index s{f (index s j) /\ filter_index_map f s j = i})

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
