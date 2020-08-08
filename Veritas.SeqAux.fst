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
        
let lemma_filter_correct_all (#a:eqtype) (f:a -> bool) (s:seq a):
  Lemma (requires (True))
        (ensures (forall (i:(seq_index (filter f s))). f (index (filter f s) i) = true)) = ()

let filter_index_map (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index (filter f s)): 
  Tot (j:seq_index s{index s j = index (filter f s) i}) =
  proj_index_map (filter f s) s (filter_is_proj_prf f s) i

let rec lemma_filter_len_monotonic (#a:eqtype) (f:a -> bool) (s:seq a) (i:nat{i <= length s}):
  Lemma (requires (True))
        (ensures (length (filter f s) >= length (filter f (prefix s i))))
        (decreases (length s)) =
  let n = length s in
  if n = 0 then ()
  else if i  = n then () // s == prefix s i
  else (
    let s' = prefix s (n - 1) in
    lemma_len_slice s 0 (n - 1);
    lemma_filter_len_monotonic f s' i
  )

let rank (#a:eqtype) (f:a -> bool)  (s:seq a) (i:nat{i <= length s})
  = length (filter f (prefix s i))

let rank_increases_by_atmost_one (#a:eqtype) (f:a -> bool) (s:seq a)
  (i:seq_index s):
  Lemma (requires (True))
        (ensures (f (index s i) && (rank f s i) + 1 = rank f s (i + 1) ||
                  not (f (index s i)) && rank f s i = rank f s (i + 1))) = ()

let filter_index_inv_map_aux (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index s{f (index s i)}):
  Tot (seq_index (filter f s)) = 
  lemma_filter_len_monotonic f s (i+1);
  lemma_len_append (filter f (prefix s i)) (create 1 (index s i));
  rank f s i

let rec lemma_filter_maps_aux (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (filter_index_map f s (filter_index_inv_map_aux f s i) = i))
        (decreases (length s)) = 
  let n = length s in
  if n = 0 then ()
  else 
    let s' = prefix s (n - 1) in
    if f (index s (n - 1)) then 
      if i = n - 1 then ()
      else 
        lemma_filter_maps_aux f s' i          
    else 
      lemma_filter_maps_aux f s' i

let filter_index_inv_map (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index s{f (index s i)}):
  Tot (j:seq_index (filter f s){index s i = index (filter f s) j}) = 
  lemma_filter_maps_aux f s i;
  filter_index_inv_map_aux f s i

(* if we know that every element of a seq satisfies f, then the same sequence is a sequence over 
 * the refinement defined by f *)
let rec seq_refine_aux (#a:Type) (f:a -> bool) (s:seq a{forall (i:seq_index s). f (index s i)})
  : Tot (seq (refine f)) (decreases (length s)) =
  let n = length s in
  if n = 0 then empty
  else append1 (seq_refine_aux f (prefix s (n - 1))) (index s (n - 1))

let seq_refine (#a:Type) (f:a -> bool) (s:seq a{all f s}): Tot (seq (refine f))
  = seq_refine_aux f s

let lemma_filter_index_map_monotonic (#a:eqtype) (f:a -> bool) (s:seq a) 
  (i:seq_index (filter f s))(j:seq_index (filter f s){j > i}):
  Lemma (filter_index_map f s i < filter_index_map f s j) = 
  lemma_proj_monotonic (filter f s) s (filter_is_proj_prf f s) i j

let lemma_filter_index_inv_map_monotonic (#a:eqtype) (f:a -> bool) (s: seq a)
  (i:seq_index s) (j: seq_index s {j > i}):
    Lemma (requires (f (index s i) /\ f (index s j)))
          (ensures (filter_index_inv_map f s i < filter_index_inv_map f s j)) = 
  lemma_filter_len_monotonic f (prefix s j) (i+1)

let lemma_filter_maps_correct (#a:eqtype) (f:a -> bool) (s: seq a) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (filter_index_map f s (filter_index_inv_map f s i) = i)) = 
  lemma_filter_maps_aux f s i

let lemma_filter_maps_correct2 (#a:eqtype) (f:a -> bool) (s: seq a) (i: seq_index (filter f s)):
  Lemma (filter_index_inv_map f s (filter_index_map f s i) = i) = 
  let j = filter_index_map f s i in
  let i' = filter_index_inv_map f s j in
  let j' = filter_index_map f s i' in
  lemma_filter_maps_correct f s j;
  assert(j = j');  
  if i < i' then
    lemma_filter_index_map_monotonic f s i i'
  else if i > i' then 
    lemma_filter_index_map_monotonic f s i' i
  else ()

let last_index_opt (#a:eqtype) (f:a -> bool) (s:seq a):
  Tot (option (i:seq_index s{f (index s i)})) =
  let fs = filter f s in
  if length fs = 0 then None
  else Some (filter_index_map f s ((length fs) - 1))

let lemma_last_index_correct1 (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index s):
  Lemma (requires (exists_sat_elems f s /\ i > last_index f s))
        (ensures (not (f (index s i)))) =
  let j = last_index f s in
  if f (index s i) then
    lemma_filter_index_inv_map_monotonic f s j i      
  else ()

let lemma_last_index_correct2 (#a:eqtype) (f:a -> bool)  (s:seq a) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (exists_sat_elems f s /\ last_index f s >= i)) =
  let n = length s in
  let ri = filter_index_inv_map f s i in
  assert (exists_sat_elems f s);
  let j = last_index f s in
  if j < i then 
    lemma_filter_index_inv_map_monotonic f s j i  
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
  let r' = filter_index_inv_map f s' li in
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
  filter_index_map f s 0

let lemma_first_index_correct1 (#a:eqtype) (f:a -> bool) (s:seq a) (i:seq_index s):
  Lemma (requires (exists_sat_elems f s /\ i < first_index f s))
        (ensures (not (f (index s i)))) =
  let fi = first_index f s in
  if f (index s i) then
    lemma_filter_index_inv_map_monotonic f s i fi
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

let rec zip_aux (#a #b: eqtype) (sa: seq a) (sb: seq b{length sb = length sa}):
  Tot (sab: (seq (a * b)){length sab = length sa}) 
  (decreases (length sa)) = 
  let n = length sa in
  if n = 0 then empty
  else
    let sa' = prefix sa (n - 1) in
    let sb' = prefix sb (n - 1) in
    append1 (zip_aux sa' sb') (index sa (n - 1), index sb (n - 1))

let zip = zip_aux

let rec lemma_zip_index_aux (#a #b: eqtype) (sa: seq a) (sb: seq b{length sa = length sb}) (i:seq_index sa):
  Lemma (requires (True))
        (ensures (fst (index (zip sa sb) i) = index sa i /\
                  snd (index (zip sa sb) i) = index sb i))
        (decreases (length sa)) =
  let n = length sa in
  if n = 0 then ()
  else if i = n - 1 then ()
  else 
    let sa' = prefix sa (n - 1) in
    let sb' = prefix sb (n - 1) in
    lemma_zip_index_aux sa' sb' i

let lemma_zip_index = lemma_zip_index_aux

let rec unzip_aux (#a #b: eqtype) (sab: seq (a * b)): 
  Tot (sasb: (seq a * seq b) {length (fst sasb) = length sab /\
                              length (snd sasb) = length sab})
  (decreases (length sab)) = 
  let n = length sab in 
  if n = 0 then (empty, empty)
  else 
    let (sa',sb') = unzip_aux (prefix sab (n - 1)) in
    let (ea, eb) = index sab (n - 1) in
    (append1 sa' ea, append1 sb' eb)

let unzip = unzip_aux

let rec lemma_unzip_index_aux (#a #b: eqtype) (sab: seq (a * b)) (i:seq_index sab):
  Lemma (requires (True))
        (ensures (fst (index sab i) = index (fst (unzip sab)) i /\
                  snd (index sab i) = index (snd (unzip sab)) i))
        (decreases (length sab)) = 
  let n = length sab in
  if n = 0 then ()
  else if i = n - 1 then ()
  else
    let sab' = prefix sab (n - 1) in
    lemma_unzip_index_aux sab' i

let lemma_unzip_index = lemma_unzip_index_aux

let lemma_zip_unzip (#a #b: eqtype) (sa: seq a) (sb: seq b{length sb = length sa}):
  Lemma (requires (True))
        (ensures ((sa, sb) = unzip (zip sa sb))) =
  let sab = zip sa sb in
  assert(length sa = length (fst (unzip sab)));
  let aux1 (i:seq_index sa):
    Lemma (requires (True)) 
          (ensures (index sa i = index (fst (unzip sab)) i))
          [SMTPat (index sa i)] = 
    lemma_unzip_index sab i;
    lemma_zip_index sa sb i
  in
  assert(equal sa (fst (unzip sab)));
  let aux2 (i:seq_index sb):
    Lemma (requires (True)) 
          (ensures (index sb i = index (snd (unzip sab)) i))
          [SMTPat (index sb i)] = 
    lemma_unzip_index sab i;
    lemma_zip_index sa sb i
  in  
  assert(equal sb (snd (unzip sab)));
  ()

let rec attach_index_aux (#a:Type) (s:seq a): Tot (seq (nat * a)) 
  (decreases (length s)) =
  let n = length s in
  if n = 0 then empty
  else
    let s' = prefix s (n - 1) in
    let e = index s (n - 1) in
    let is' = attach_index_aux s' in
    append1 is' (n - 1, e)
  
let attach_index = attach_index_aux

let rec lemma_attach_len_aux (#a:Type) (s: seq a):
  Lemma (requires (True))
        (ensures (length (attach_index s) = length s))
        (decreases (length s)) = 
  let n = length s in
  if n = 0 then ()
  else lemma_attach_len_aux (prefix s (n - 1))

let lemma_attach_len = lemma_attach_len_aux

let rec lemma_attach_correct_aux (#a:Type) (s: seq a) (i: seq_index s):
  Lemma (requires (True))
        (ensures (length (attach_index s) = length s /\        
                  snd (index (attach_index s) i) == index s i /\
                  fst (index (attach_index s) i) = i))
        (decreases (length s)) = 
  lemma_attach_len s;
  let n = length s in
  if n = 0 then ()
  else if i = n - 1 then ()
  else lemma_attach_correct_aux (prefix s (n - 1)) i

let lemma_attach_correct = lemma_attach_correct_aux

let rec reduce_aux (#a:Type) (#b:Type) (b0: b) (f: a -> b -> b) (s: seq a): 
  Tot b (decreases (length s)) = 
  let n = length s in
  if n = 0 then b0
  else
    let s' = prefix s (n - 1) in
    let b' = reduce_aux b0 f s' in
    let e = index s (n - 1) in
    f e b' 

let reduce = reduce_aux

let lemma_reduce_empty (#a:Type) (#b:eqtype) (b0:b) (f:a -> b -> b):
  Lemma (reduce b0 f (empty #a) = b0) = ()

let rec lemma_reduce_prefix_aux (#a:Type) (#b:eqtype) (b0: b) (f: a -> b -> b) (s: seq a) (i: seq_index s):
  Lemma (requires True)
        (ensures (reduce b0 f s = reduce (reduce b0 f (prefix s i)) f (suffix s (length s - i))))
        (decreases (length s)) = 
  let n = length s in
  if n = 0 then ()
  else 
    let s' = prefix s (n - 1) in
    let b' = reduce b0 f s' in
    let e = index s (n - 1) in
    if i = n - 1 then ()
    else 
      lemma_reduce_prefix_aux b0 f s' i

let lemma_reduce_prefix = lemma_reduce_prefix_aux

let rec lemma_reduce_property_closure_aux (#a:Type) (#b:eqtype) (p: b -> bool) (b0:b) (f: a -> b -> b) (s: seq a):
  Lemma (requires (p b0 /\ (forall (x:a). forall (y:b). (p y ==> p (f x y)))))
        (ensures (p (reduce b0 f s)))
        (decreases (length s)) = 
  let n = length s in
  if n = 0 then ()
  else
    lemma_reduce_property_closure_aux p b0 f (prefix s (n - 1))

let lemma_reduce_property_closure = lemma_reduce_property_closure_aux

let lemma_reduce_identity (#a:Type) (#b:eqtype) (b0: b) (f: a -> b -> b) (s: seq a):
  Lemma (requires (forall (x:a). f x b0 = b0))
        (ensures (reduce b0 f s = b0)) = 
  lemma_reduce_property_closure (fun y -> y = b0) b0 f s
