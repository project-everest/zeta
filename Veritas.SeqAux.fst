module Veritas.SeqAux

open FStar.Classical
open FStar.Seq

let prefix (#a:Type) (s:seq a) (i:nat{i <= length s}) = slice s 0 i

let lemma_prefix_index (#a:Type) (s:seq a) (i:nat{i <= length s}) (j:nat{j < i}):
  Lemma (requires (True))
        (ensures (index (prefix s i) j == index s j)) =
  lemma_index_slice s 0 i j

let lemma_prefix_prefix (#a:Type) (s:seq a) (i:nat{i <= length s}) (j:nat{j <= i}):
  Lemma (requires (True))
        (ensures (prefix (prefix s i) j == prefix s j)) = 
  let pij = prefix (prefix s i) j in
  let pj = prefix s j in
  let pi = prefix s i in
  let aux (k:nat{k < j}):
    Lemma (index pij k == index pj k) = 
    lemma_prefix_index s j k;
    lemma_prefix_index s i k;
    lemma_prefix_index pi j k
  in
  forall_intro aux; lemma_eq_intro pij pj

let lemma_fullprefix_equal (#a:Type) (s:seq a):
  Lemma (requires (True))
        (ensures (prefix s (length s) == s)) = 
  let n = length s in
  let p = prefix s n in
  let aux (k:nat{k < n}):
    Lemma (index p k == index s k) = 
    lemma_prefix_index s n k
  in
  forall_intro aux; lemma_eq_intro s p

let suffix (#a:Type) (s:seq a) (i:nat{i <= length s}) =
  slice s (length s - i) (length s)

let lemma_suffix_index (#a:Type) (s:seq a) (i:nat{i <= length s}) (j:nat{j < i}):
  Lemma (requires (True))
        (ensures (index (suffix s i) j == index s (length s - i + j))) =
  lemma_index_slice s (length s - i) (length s) j

(*
 * TODO: For some reason a direct recursive implementation of filter
 * fails to compile
 *)
let rec filter_aux (#a:eqtype) (f:a -> bool) (s:seq a) : Tot (seq (refine f))
  (decreases (length s)) =
  let n = length s in
  if n = 0 then empty
  else
    let e = index s (n - 1) in
    if f e then
      append (filter_aux f (prefix s (n - 1))) (create 1 e)
    else
      filter_aux f (prefix s (n - 1))

let filter (#a:eqtype) (f:a -> bool) (s:seq a) : Tot (seq (refine f))  = filter_aux f s

let rec filter_len_monotonic (#a:eqtype) (f:a -> bool) (s:seq a) (i:nat{i <= length s}):
  Lemma (requires (True))
        (ensures (length (filter f s) >= length (filter f (prefix s i))))
        (decreases (length s)) =
  let n = length s in
  if n = 0 then ()
  else if i  = n then () // s == prefix s i
  else (
    let s' = prefix s (n - 1) in
    lemma_len_slice s 0 (n - 1);
    filter_len_monotonic f s' i
  )

let rank (#a:eqtype) (f:a -> bool)  (s:seq a) (i:nat{i <= length s})
  = length (filter f (prefix s i))

let filter_index_map_aux (#a:eqtype) (f:a -> bool)  (s:seq a)
  (i:seq_index s{f (index s i)}):
  Tot (seq_index (filter f s)) =
  filter_len_monotonic f s (i+1);
  lemma_len_append (filter f (prefix s i)) (create 1 (index s i));
  rank f s i

let rec filter_index_map_correct (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (index s i = index (filter f s) (filter_index_map_aux f s i)))
        (decreases (length s)) =
  let n = length s in
  if n = 0 then ()
  else if i = n - 1 then ()
  else filter_index_map_correct f (prefix s (n - 1)) i

let filter_index_map (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index s{f (index s i)}):
  Tot (j:seq_index (filter f s){index s i = index (filter f s) j}) =
  filter_index_map_correct f s i;
  filter_index_map_aux f s i
         
let filter_index_map_monotonic (#a:eqtype) (f:a -> bool) (s:seq a)
  (i:seq_index s) (j:seq_index s{j > i}):
  Lemma (requires (f (index s i) && f (index s j)))
        (ensures (filter_index_map f s i < filter_index_map f s j)) =
  filter_len_monotonic f (prefix s j) (i + 1)

let rank_increases_by_atmost_one (#a:eqtype) (f:a -> bool) (s:seq a)
  (i:seq_index s):
  Lemma (requires (True))
        (ensures (f (index s i) && (rank f s i) + 1 = rank f s (i + 1) ||
                  not (f (index s i)) && rank f s i = rank f s (i + 1))) = ()

let rec rank_search (#a:eqtype) (f:a -> bool) (s:seq a)
                (r:seq_index (filter f s))
                (i:nat{i <= length s && rank f s i > r})
  : Tot (j:seq_index s{rank f s j = r && f (index s j)})
    (decreases i) =
  assert (i > 0);
  if rank f s (i - 1) = r then (i - 1)
  else (
    rank_increases_by_atmost_one f s (i - 1);
    rank_search f s r (i - 1)
  )

let filter_index_inv_map (#a:eqtype) (f:a -> bool)  (s:seq a) (i:seq_index (filter f s))
  : Tot (j:seq_index s{f (index s j) && filter_index_map f s j = i}) =
  rank_search f s i (length s)

let filter_index_inv_map_monotonic (#a:eqtype) (f:a -> bool) (s: seq a)
  (i:seq_index (filter f s)) (j: seq_index (filter f s) {j > i}):
    Lemma (requires (True))
          (ensures (filter_index_inv_map f s i < filter_index_inv_map f s j)) = 
  let i' = filter_index_inv_map f s i in
  let j' = filter_index_inv_map f s j in
  if i' < j' then () // nothing to prove
  else if i' > j' then
    filter_index_map_monotonic f s j' i'
  else ()

let lemma_filter_maps_correct (#a:eqtype) (f:a -> bool) (s: seq a) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (filter_index_inv_map f s (filter_index_map f s i) = i)) = 
  let i' = filter_index_map f s i in
  let i2 = filter_index_inv_map f s i' in
  if i2 < i then 
    filter_index_map_monotonic f s i2 i
  else if i2 > i then
    filter_index_map_monotonic f s i i2
  else ()

let last_index_opt (#a:eqtype) (f:a -> bool) (s:seq a):
  Tot (option (i:seq_index s{f (index s i)})) =
  let fs = filter f s in
  if length fs = 0 then None
  else Some (filter_index_inv_map f s ((length fs) - 1))

let lemma_last_index_correct1 (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index s):
  Lemma (requires (exists_sat_elems f s /\ i > last_index f s))
        (ensures (not (f (index s i)))) =
  let j = last_index f s in
  if f (index s i) then
    filter_index_map_monotonic f s j i
  else ()

let lemma_last_index_correct2 (#a:eqtype) (f:a -> bool)  (s:seq a) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (exists_sat_elems f s /\ last_index f s >= i)) =
  let n = length s in
  let ri = filter_index_map f s i in
  assert (exists_sat_elems f s);
  let j = last_index f s in
  if j < i then
    filter_index_map_monotonic f s j i
  else ()

let lemma_last_index_prefix (#a:eqtype) (f:a -> bool) (s:seq a) (i:nat{i <= length s}):
  Lemma (requires (exists_sat_elems f s /\ i > last_index f s))
        (ensures (exists_sat_elems f (prefix s i) /\
                  last_index f s = last_index f (prefix s i))) =
  let li = last_index f s in
  let s' = prefix s i in
  lemma_prefix_index s i li;
  assert(f (index s' li));
  assert(li < length s');
  let r' = filter_index_map f s' li in
  assert(exists_sat_elems f s');
  let li' = last_index f s' in
  if li < li' then (
    lemma_prefix_index s i li';
    lemma_last_index_correct1 f s li'
  )
  else if li > li' then
    lemma_last_index_correct1 f s' li
  else ()

let lemma_not_exists_prefix (#a:eqtype) (f:a -> bool) (s:seq a) (i:nat{i <= length s}):
  Lemma (requires (not (exists_sat_elems f s)))
        (ensures (not (exists_sat_elems f (prefix s i)))) = 
  let s' = prefix s i in
  if exists_sat_elems f s' then (
    let li' = last_index f s' in
    lemma_prefix_index s i li';
    lemma_last_index_correct2 f s li'
  )
  else ()
  

let rec map_aux (#a #b:Type) (f:a -> b) (s:seq a): 
  Tot (s':seq b{length s' = length s}) 
  (decreases (length s))
  = 
  let n = length s in
  if n = 0 then empty
  else 
    let ps = prefix s (n - 1) in
    let e = index s (n - 1) in
    append (map_aux f ps) (create 1 (f e))

let map (#a #b:Type) (f:a -> b) (s:seq a): Tot (s':seq b{length s' = length s}) = map_aux f s

let rec lemma_map_index_aux (#a #b: Type) (f:a -> b) (s:seq a) (i:seq_index s):
  Lemma (requires (True))
        (ensures (f (index s i) == index (map f s) i))
        (decreases (length s)) = 
  let n = length s in
  if n = 0 then ()
  else if i = n - 1 then ()
  else
    let s' = prefix s (n - 1) in
    let e = index s (n - 1) in
    lemma_map_index_aux f s' i;
    lemma_prefix_index s (n - 1) i;
    lemma_index_app1 (map f s') (create 1 (f e)) i

let lemma_map_index (#a #b: Type) (f:a -> b) (s:seq a) (i:seq_index s):
  Lemma (requires (True))
        (ensures (f (index s i) == index (map f s) i)) = 
  lemma_map_index_aux f s i
