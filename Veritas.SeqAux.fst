module Veritas.SeqAux

open FStar.Classical
open FStar.Seq
open FStar.Squash

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

let lemma_prefix_append (#a:Type) (s1 s2: seq a):
  Lemma (prefix (append s1 s2) (length s1) == s1) =
  // triggers an SMT pat that provides what we need
  assert(equal (prefix (append s1 s2) (length s1)) s1);
  ()

let suffix (#a:Type) (s:seq a) (i:nat{i <= length s}) =
  slice s (length s - i) (length s)

let lemma_suffix_index (#a:Type) (s:seq a) (i:nat{i <= length s}) (j:nat{j < i}):
  Lemma (requires (True))
        (ensures (index (suffix s i) j == index s (length s - i + j))) =
  lemma_index_slice s (length s - i) (length s) j

let lemma_prefix_suffix (#a:Type) (s:seq a) (i:nat{i <= length s}):
  Lemma (requires (True))
        (ensures (append (prefix s i) (suffix s (length s - i)) == s)) =
  assert(equal (append (prefix s i) (suffix s (length s - i))) s);
  ()

(* append a single element to the end of a sequence *)
let append1 (#a:eqtype) (s:seq a) (x:a): s':(seq a){length s' = length s + 1} =
  append s (create 1 x)

type proj (#a:eqtype): seq a -> seq a -> Type0 =
  | PrjEmpty: proj (empty #a) (empty #a)
  | PrjIncl: ss: seq a -> s:seq a -> prf:proj ss s -> x:a -> proj (append1 ss x) (append1 s x)
  | PrjSkip: ss: seq a -> s:seq a -> prf:proj ss s -> x:a -> proj ss (append1 s x)

let rec proj_index_map_aux (#a:eqtype) (ss: seq a) (s: seq a) (prf:proj ss s) (i:seq_index ss) :
  Tot (j:seq_index s{index s j = index ss i})
  (decreases (length s))
  =
  let n = length s in
  let ns = length ss in
  match prf with
  | PrjIncl ss' s' prf' e ->
    if i = ns - 1 then
      n - 1
    else
      proj_index_map_aux ss' s' prf' i
  | PrjSkip ss' s' prf' x -> proj_index_map_aux ss' s' prf' i

let proj_index_map (#a:eqtype) (ss s: seq a) (prf: proj ss s) (i: seq_index ss) = 
  proj_index_map_aux ss s prf i

(* the mapping we construct above is monotonic *)
let rec lemma_proj_monotonic_aux (#a:eqtype) (ss s: seq a) (prf: proj ss s) (i1 i2: seq_index ss):
  Lemma (requires (i1 < i2))
        (ensures (proj_index_map ss s prf i1 < proj_index_map ss s prf i2)) 
        (decreases prf) = 
  match prf with
  | PrjIncl ss' s' prf' _ -> 
    if i2 = length ss - 1 then ()
    else lemma_proj_monotonic_aux ss' s' prf' i1 i2
  | PrjSkip ss' s' prf' _ -> lemma_proj_monotonic_aux ss' s' prf' i1 i2

let lemma_proj_monotonic (#a:eqtype) (ss s: seq a) (prf: proj ss s) (i1 i2: seq_index ss):
  Lemma (requires (i1 < i2))
        (ensures (proj_index_map ss s prf i1 < proj_index_map ss s prf i2)) = 
  lemma_proj_monotonic_aux ss s prf i1 i2

let rec lemma_proj_length_aux (#a:eqtype) (ss s: seq a) (prf: proj ss s): 
  Lemma (requires (True)) 
        (ensures (length ss <= length s))
        (decreases prf) = 
  match prf with
  | PrjEmpty -> ()
  | PrjIncl ss' s' prf' _ -> lemma_proj_length_aux ss' s' prf'
  | PrjSkip ss' s' prf' _ -> lemma_proj_length_aux ss' s' prf'

let lemma_as_squash #a #b (lem: (a -> Lemma b)) (x:a)
  : GTot (squash b)
  = lem x

let lemma_proj_length (#a:eqtype) (ss: seq a) (s:seq a{proj ss s}):
  Lemma (requires (True))
        (ensures (length ss <= length s)) = 
  bind_squash () (lemma_as_squash #(proj ss s) #(length ss <= length s) (lemma_proj_length_aux ss s))

let rec filter_aux (#a:eqtype) (f:a -> bool) (s:seq a) : Tot (seq a)
  (decreases (length s)) =
  let n = length s in
  if n = 0 then empty
  else
    let e = index s (n - 1) in
    if f e then
      append1 (filter_aux f (prefix s (n - 1))) e
    else
      filter_aux f (prefix s (n - 1))

let filter (#a:eqtype) (f:a -> bool) (s:seq a) : Tot (seq a)  = filter_aux f s

let rec filter_is_proj_aux (#a:eqtype) (f:a -> bool) (s:seq a): Tot (proj (filter f s) s)
  (decreases (length s)) =
  let n = length s in
  let fs = filter f s in
  if n = 0 then (
    lemma_empty s;
    PrjEmpty #a
  )
  else (

    let e = index s (n - 1) in
    let s' = prefix s (n - 1) in
    let fs' = filter f s' in
    assert (equal (append1 s' e) s);
    let prf = filter_is_proj_aux f s' in
    if f e then
      PrjIncl fs' s' prf e
    else
      PrjSkip fs' s' prf e
  )

let lemma_filter_is_proj (#a:eqtype) (f:a -> bool) (s:seq a):
  Lemma (proj (filter f s) s) = return_squash (filter_is_proj_aux f s)

let filter_is_proj_prf (#a:eqtype) (f:a -> bool) (s: seq a) = filter_is_proj_aux f s

(* every index in the filtered sequence satisfies the filter predicate *)
let rec lemma_filter_correct1_aux (#a: eqtype) (f:a -> bool) (s:seq a) (i:seq_index (filter f s)):
  Lemma (requires (True))
        (ensures (f (index (filter f s) i) = true))
        (decreases (length s)) = 
  let n = length s in
  let fs = filter f s in
  if n = 0 then ()
  else 
    let s' = prefix s (n - 1) in
    let e = index s (n - 1) in
    if f e then
      if i = (length fs) - 1 then ()
      else
        lemma_filter_correct1_aux f s' i
    else
      lemma_filter_correct1_aux f s' i

let lemma_filter_correct1 (#a: eqtype) (f:a -> bool) (s:seq a) (i:seq_index (filter f s)):
  Lemma (requires (True))
        (ensures (f (index (filter f s) i) = true)) = lemma_filter_correct1_aux f s i
        


(*

let rec projection_aux (#a:eqtype) (ss s: seq a): Tot bool (decreases (length s)) =
  let nss = length ss in
  let ns = length s in
  if nss = 0 then true
  else if ns = 0 then false
  else
    let es = index s (ns - 1) in
    let ess = index ss (nss - 1) in
    if projection_aux ss (prefix s (ns - 1)) then true
    else if es = ess then projection_aux (prefix ss (nss - 1)) (prefix s (ns - 1))
    else false

let projection (#a:eqtype) (ss s: seq a) = projection_aux ss s

let rec lemma_filter_is_projection_aux (#a:eqtype) (f:a -> bool) (s:seq a):
  Lemma (requires (True))
        (ensures (projection (filter f s) s))
        (decreases (length s)) =
  let n = length s in
  if n = 0 then ()
  else
    let e = index s (n - 1) in
    let s' = prefix s (n - 1) in
    let fs' = filter f s' in
    if f e then (
      lemma_filter_is_projection_aux f s';
      lemma_prefix_append fs' (create 1 e);
      ()
    )
    else
      lemma_filter_is_projection_aux f s'

let lemma_filter_is_projection (#a:eqtype) (f:a -> bool) (s:seq a):
  Lemma (projection (filter f s) s) = lemma_filter_is_projection_aux f s

(* mapping from a subsequence index to the corresponding index in the base sequence *)
let rec projection_index_map_aux (#a:eqtype) (ss: seq a) (s: seq a{projection ss s}) (i:seq_index ss):
  Tot (j:seq_index s{index s j = index ss i})
  (decreases (length s)) =
  let n = length s in
  let ns = length ss in
  if ns = 0 then 0       (* contradiction since i < ns *)
  else if n = 0 then 0   (* contradiction since (projection ss s) is false *)
  else
    let s' = prefix s (n - 1) in
    let e = index s (n - 1) in
    let ss' = prefix ss (ns - 1) in
    let es = index ss (ns - 1) in
    if projection ss s' then
      projection_index_map_aux ss s' i
    else (
      assert (e = es);
      if i = ns - 1 then n - 1
      else projection_index_map_aux ss' s' i
    )

(* mapping from a subsequence index to the corresponding index in the base sequence *)
let projection_index_map (#a:eqtype) (ss: seq a) (s: seq a{projection ss s}) (i:seq_index ss):
  Tot (j:seq_index s{index s j = index ss i}) = projection_index_map_aux ss s i

let lemma_projection_monotonic (#a:eqtype) (ss: seq a) (s:seq a{projection ss s}) (i1 i2: seq_index ss):
  Lemma (requires (i1 < i2))
        (ensures (projection_index_map ss s i1 < projection_index_map ss s i2))


(* every index in the filtered sequence satisfies the filter predicate
let rec lemma_filter_correct1_aux (#a:Type) (f:a -> bool) (s:seq a) (i:seq_index (filter f s)):
  Lemma (requires (True))
        (ensures (f (index (filter f s) i) = true))
        (decreases (length s)) =
  let n = length s in
  if n = 0 then ()
  else
    let e = index s (n-  1) in
    if f e then
      admit()
    else
      admit()

*)



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

let lemma_exists_prefix_implies_exists (#a:eqtype) (f:a -> bool) (s:seq a) (i:nat{i <= length s}):
  Lemma (requires (exists_sat_elems f (prefix s i)))
        (ensures (exists_sat_elems f s)) =
  let s' = prefix s i in
  let li = last_index f s' in
  lemma_last_index_correct2 f s li

let lemma_last_index_last_elem_nsat (#a:eqtype) (f:a -> bool) (s:seq a{length s > 0}):
  Lemma (requires (not (f (index s (length s - 1)))))
        (ensures ((exists_sat_elems f s ==> last_index f s < length s - 1) /\
                  exists_sat_elems f s = exists_sat_elems f (prefix s (length s - 1)))) =
  if exists_sat_elems f s then
    let li = last_index f s in
    ()
  else ()

let lemma_last_index_last_elem_sat (#a:eqtype) (f:a -> bool) (s:seq a{length s > 0}):
  Lemma (requires (f (index s (length s - 1))))
        (ensures (exists_sat_elems f s /\ last_index f s = length s - 1)) =
  let n = length s in
  lemma_last_index_correct2 f s (n - 1)

let first_index (#a:eqtype) (f:a -> bool) (s:seq a{exists_sat_elems f s})
  : Tot (i:seq_index s{f (index s i)}) =
  filter_index_inv_map f s 0

let lemma_first_index_correct1 (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index s):
  Lemma (requires (exists_sat_elems f s /\ i < first_index f s))
        (ensures (not (f (index s i)))) =
  let fi = first_index f s in
  if f (index s i) then
    filter_index_map_monotonic f s i fi
  else ()

let lemma_first_index_correct2 (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (exists_sat_elems f s /\ first_index f s <= i)) =
  lemma_last_index_correct2 f s i;
  let fi = first_index f s in
  if fi > i then
    lemma_first_index_correct1 f s i
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
*)
