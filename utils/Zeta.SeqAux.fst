module Zeta.SeqAux
#push-options "--print_universes"

open FStar.Classical
open FStar.Seq
open FStar.Squash

let prefix (#a:Type) (s:seq a) (i:nat{i <= length s}) = slice s 0 i

let prefix_slice #_ _ _ = ()

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

let lemma_hprefix_append_telem (#a:Type) (s: seq a{length s > 0}):
  Lemma (ensures (let s' = hprefix s in
                  let e = telem s in
                  s == append1 s' e)) =
  let s' = hprefix s in
  let e = telem s in
  lemma_prefix1_append s' e;
  let s2 = append1 s' e in
  assert(length s = length s2);
  let aux (i: seq_index s):
    Lemma (ensures (index s i == index s2 i))
          [SMTPat (index s i == index s2 i)] = ()
  in
  lemma_eq_intro s s2

let lemma_prefix0_empty (#a:Type) (s: seq a):
  Lemma (prefix s 0 == empty #a) = ()

let lemma_prefix_create (#a:Type) (n:nat) (v:a) (i:nat{i <= n}) 
  : Lemma (prefix (create n v) i == create i v)
  = let l1 = prefix (create n v) i in
    let l2 = create i v in
    let aux (k:nat{k < i}) : Lemma (index l1 k == index l2 k) = () in
    forall_intro aux; lemma_eq_intro l1 l2

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

type proj (#a:Type u#a): seq a -> seq a -> Type u#a =
  | PrjEmpty: proj (empty #a) (empty #a)
  | PrjIncl: ss: seq a -> s:seq a -> prf:proj ss s -> x:a -> proj (append1 ss x) (append1 s x)
  | PrjSkip: ss: seq a -> s:seq a -> prf:proj ss s -> x:a -> proj ss (append1 s x)

let rec proj_index_map_aux (#a:Type) (ss: seq a) (s: seq a) (prf:proj ss s) (i:seq_index ss) :
  Tot (j:seq_index s{index s j == index ss i})
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

let proj_index_map (#a:Type) (ss s: seq a) (prf: proj ss s) (i: seq_index ss) =
  proj_index_map_aux ss s prf i

(* the mapping we construct above is monotonic *)
let rec lemma_proj_monotonic_aux (#a:Type) (ss s: seq a) (prf: proj ss s) (i1 i2: seq_index ss):
  Lemma (requires (i1 < i2))
        (ensures (proj_index_map ss s prf i1 < proj_index_map ss s prf i2))
        (decreases prf) =
  match prf with
  | PrjIncl ss' s' prf' _ ->
    if i2 = length ss - 1 then ()
    else lemma_proj_monotonic_aux ss' s' prf' i1 i2
  | PrjSkip ss' s' prf' _ -> lemma_proj_monotonic_aux ss' s' prf' i1 i2

let lemma_proj_monotonic (#a:Type) (ss s: seq a) (prf: proj ss s) (i1 i2: seq_index ss):
  Lemma (requires (i1 < i2))
        (ensures (proj_index_map ss s prf i1 < proj_index_map ss s prf i2)) =
  lemma_proj_monotonic_aux ss s prf i1 i2

let rec lemma_proj_length_aux (#a:Type) (ss s: seq a) (prf: proj ss s):
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

let lemma_proj_length (#a:Type) (ss: seq a) (s:seq a{proj ss s}):
  Lemma (requires (True))
        (ensures (length ss <= length s)) =
  bind_squash () (lemma_as_squash #(proj ss s) #(length ss <= length s) (lemma_proj_length_aux ss s))

let rec filter_aux (#a:Type) (f:a -> bool) (s:seq a) : Tot (seq a)
  (decreases (length s)) =
  let n = length s in
  if n = 0 then empty
  else
    let e = index s (n - 1) in
    if f e then
      append1 (filter_aux f (prefix s (n - 1))) e
    else
      filter_aux f (prefix s (n - 1))

let filter (#a:Type) (f:a -> bool) (s:seq a) : Tot (seq a)  = filter_aux f s

let rec filter_is_proj_aux (#a:Type) (f:a -> bool) (s:seq a): Tot (proj (filter f s) s)
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

let lemma_filter_is_proj (#a:Type) (f:a -> bool) (s:seq a):
  squash (proj (filter f s) s) = return_squash (filter_is_proj_aux f s)

let filter_is_proj_prf (#a:Type) (f:a -> bool) (s: seq a) = filter_is_proj_aux f s

(* every index in the filtered sequence satisfies the filter predicate *)
let rec lemma_filter_correct1_aux (#a: Type) (f:a -> bool) (s:seq a) (i:seq_index (filter f s)):
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
      
let lemma_filter_correct1 (#a: Type) (f:a -> bool) (s:seq a) (i:seq_index (filter f s)):
  Lemma (requires (True))
        (ensures (f (index (filter f s) i) = true)) = lemma_filter_correct1_aux f s i

let lemma_filter_correct_all (#a:Type) (f:a -> bool) (s:seq a):
  Lemma (requires (True))
        (ensures (forall (i:(seq_index (filter f s))). f (index (filter f s) i) = true)) = ()

let rec lemma_filter_all_not_aux (#a: Type) (f:a -> bool) (s:seq a):
  Lemma (requires (filter f s `Seq.equal` empty))
        (ensures (forall (i:seq_index s). not (f (index s i))))
        (decreases (length s)) =
  let n = length s in
  if n = 0 then ()
  else let e = index s (n - 1) in
       let s' = prefix s (n - 1) in
       if not (f e) 
       then (
         assert (equal (append1 s' e) s);
         lemma_filter_all_not_aux f s'
       )

let lemma_filter_all_not (#a:Type) (f:a -> bool) (s:seq a)
  : Lemma (requires filter f s `equal` empty)
          (ensures forall (i:seq_index s). not (f (index s i)))
  = lemma_filter_all_not_aux f s

let rec lemma_filter_all_not_inv_aux (#a: Type) (f:a -> bool) (s:seq a):
  Lemma (requires (forall (i:seq_index s). not (f (index s i))))
        (ensures (filter f s `Seq.equal` empty))
        (decreases (length s)) =
  let n = length s in
  if n = 0 then ()
  else let e = index s (n - 1) in
       let s' = prefix s (n - 1) in
       if not (f e) 
       then lemma_filter_all_not_inv_aux f s'

let lemma_filter_all_not_inv (#a:Type) (f:a->bool) (s:seq a)
  : Lemma (requires (forall (i:seq_index s). not (f (index s i))))
          (ensures (equal (filter f s) empty))
  = lemma_filter_all_not_inv_aux f s

let lemma_filter_exists (#a:Type) (f:a -> bool) (s:seq a):
  Lemma (requires (exists (i:seq_index s). f (index s i)))
        (ensures (length (filter f s) > 0)) =
  if length (filter f s) = 0
  then lemma_filter_all_not f s

let rec lemma_filter_unique_aux (#a:Type) (f:a -> bool) (s:seq a) (i:seq_index s)
  : Lemma (requires (f (index s i) /\ (forall j. j <> i ==> not (f (index s j)))))
          (ensures (filter f s == create 1 (index s i)))
          (decreases (length s)) =
  let n = length s in
  if n = 0 then ()
  else let e = index s (n - 1) in
       let s' = prefix s (n - 1) in
       if i < n - 1 
       then lemma_filter_unique_aux f s' i
       else (
         lemma_filter_all_not_inv f s';
         assert (equal (append1 empty e) (create 1 (index s i)))
       )

let lemma_filter_unique (#a:Type) (f:a->bool) (s: seq a) (i:seq_index s)
  : Lemma (requires (f (index s i) /\ (forall j. j <> i ==> not (f (index s j)))))
          (ensures (filter f s == create 1 (index s i)))
  = lemma_filter_unique_aux f s i

let filter_index_map (#a:Type) (f:a -> bool) (s:seq a) (i:seq_index (filter f s)):
  Tot (j:seq_index s{index s j == index (filter f s) i}) =
  proj_index_map (filter f s) s (filter_is_proj_prf f s) i

let rec lemma_filter_len_monotonic (#a:Type) (f:a -> bool) (s:seq a) (i:nat{i <= length s}):
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

let rank (#a:Type) (f:a -> bool)  (s:seq a) (i:nat{i <= length s})
  = length (filter f (prefix s i))

let rank_increases_by_atmost_one (#a:Type) (f:a -> bool) (s:seq a)
  (i:seq_index s):
  Lemma (requires (True))
        (ensures (f (index s i) && (rank f s i) + 1 = rank f s (i + 1) ||
                  not (f (index s i)) && rank f s i = rank f s (i + 1))) = ()

let filter_index_inv_map_aux (#a:Type) (f:a -> bool) (s:seq a) (i:seq_index s{f (index s i)}):
  Tot (seq_index (filter f s)) =
  lemma_filter_len_monotonic f s (i+1);
  lemma_len_append (filter f (prefix s i)) (create 1 (index s i));
  rank f s i

let rec lemma_filter_maps_aux (#a:Type) (f:a -> bool) (s:seq a) (i:seq_index s):
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

let filter_index_inv_map (#a:Type) (f:a -> bool) (s:seq a) (i:seq_index s{f (index s i)}):
  Tot (j:seq_index (filter f s){index s i == index (filter f s) j}) =
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

let rec lemma_seq_refine_len_aux (#a:Type) (f:a->bool) (s:seq a{all f s}):
  Lemma (requires True)
        (ensures (length (seq_refine f s) = length s))
        (decreases (length s)) =
  let n = length s in
  if n = 0 then ()
  else
    lemma_seq_refine_len_aux f (prefix s (n - 1))

let lemma_seq_refine_len = lemma_seq_refine_len_aux

let rec lemma_seq_refine_equal_aux (#a:Type) (f:a->bool) (s:seq a{all f s}) (i:seq_index s):
  Lemma (requires True)
        (ensures (index (seq_refine f s) i == index s i))
        (decreases (length s)) =
  let n = length s in
  if n = 0 then ()
  else if i = n - 1 then ()
  else lemma_seq_refine_equal_aux f (prefix s (n - 1)) i

let lemma_seq_refine_equal = lemma_seq_refine_equal_aux

let lemma_filter_index_map_monotonic (#a:Type) (f:a -> bool) (s:seq a)
  (i:seq_index (filter f s))(j:seq_index (filter f s){j > i}):
  Lemma (filter_index_map f s i < filter_index_map f s j) =
  lemma_proj_monotonic (filter f s) s (filter_is_proj_prf f s) i j

let lemma_filter_index_inv_map_monotonic (#a:Type) (f:a -> bool) (s: seq a)
  (i:seq_index s) (j: seq_index s {j > i}):
    Lemma (requires (f (index s i) /\ f (index s j)))
          (ensures (filter_index_inv_map f s i < filter_index_inv_map f s j)) =
  lemma_filter_len_monotonic f (prefix s j) (i+1)

let lemma_filter_maps_correct (#a:Type) (f:a -> bool) (s: seq a) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (filter_index_map f s (filter_index_inv_map f s i) = i)) =
  lemma_filter_maps_aux f s i

let lemma_filter_maps_correct2 (#a:Type) (f:a -> bool) (s: seq a) (i: seq_index (filter f s)):
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

let lemma_filter_empty (#a:Type) (f:a -> bool):
  Lemma (filter f (empty #a) == (empty #a)) =
  let se = (empty #a) in
  let fse = filter f se in
  lemma_filter_is_proj #a f se;
  lemma_proj_length fse se;
  lemma_empty fse

let rec lemma_filter_prefix_aux (#a:Type) (f:a -> bool) (s: seq a) (ps: seq a{is_prefix s ps}):
  Lemma (requires True)
        (ensures (is_prefix (filter f s) (filter f ps)))
        (decreases (length s))
        =
  let n = length s in
  let fs = filter f s in
  let fps = filter f ps in
  let i = length ps in
  if n = 0 then ()
  else if i = n then ()
  else (
    let s' = prefix s (n - 1) in
    lemma_filter_prefix_aux f s' ps;
    let e = index s (n - 1) in
    if f e then lemma_prefix_append (filter f s') (create 1 e)
    else ()
  )

let lemma_filter_prefix = lemma_filter_prefix_aux

let lemma_filter_prefix_comm (#a:Type) (f:a->bool) (s: seq a) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (filter f (prefix s i) == prefix (filter f s) (filter_index_inv_map f s i))) =
  lemma_filter_prefix f s (prefix s i)

let lemma_filter_prefix_comm2 (#a:Type) (f:a->bool) (s: seq a) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (filter f (prefix s (i+1)) == prefix (filter f s) (1 + (filter_index_inv_map f s i)))) = 
  rank_increases_by_atmost_one f s i;
  lemma_filter_prefix f s (prefix s (i + 1))

let lemma_filter_extend1 (#a:Type) (f:a -> bool) (s:seq a{length s > 0}):
  Lemma (requires (not (f (index s (length s - 1)))))
        (ensures (filter f s == filter f (prefix s (length s - 1)))) = ()

let lemma_filter_extend2 (#a:Type) (f:a -> bool) (s:seq a{length s > 0}):
  Lemma (requires (f (index s (length s - 1))))
        (ensures (filter f s == append1 (filter f (prefix s (length s - 1))) (index s (length s - 1))))
   = ()

let rec lemma_filter_update_length_aux (#a:Type) (f:a -> bool) (s: seq a) (i:seq_index s) (v:a)
  : Lemma (requires (f v = f (index s i)))
          (ensures (length (filter f s) = length (filter f (upd s i v))))
          (decreases (length s))
  = let n = length s in
    if n > 0 &&  i < n - 1
      then lemma_filter_update_length_aux f (prefix s (n - 1)) i v

let lemma_filter_update_length (#a:Type) (f:a -> bool) (s:seq a) (i:seq_index s) (v:a)
  : Lemma (requires (f v = f (index s i)))
          (ensures (length (filter f s) = length (filter f (upd s i v))))
  = lemma_filter_update_length_aux f s i v

#push-options "--z3rlimit_factor 2"
let rec lemma_filter_update_index_eq_aux (#a:Type) (f:a -> bool) (s: seq a) (i:seq_index s) (v:a)
  : Lemma (requires (f v /\ f (index s i)))
          (ensures (index (filter f (upd s i v)) (filter_index_inv_map f s i) == v))
          (decreases (length s))
  = let n = length s in
    if n > 0 && i < n - 1 
    then lemma_filter_update_index_eq_aux f (prefix s (n - 1)) i v
#pop-options

let lemma_filter_update_index_eq (#a:Type) (f:a -> bool) (s:seq a) (i:seq_index s) (v:a)
  : Lemma (requires (f v /\ f (index s i)))
          (ensures (index (filter f (upd s i v)) (filter_index_inv_map f s i) == v))
  = lemma_filter_update_index_eq_aux f s i v

(*
let lemma_filter_update_index_neq (#a:Type) (f:a -> bool) (s:seq a) (i:seq_index s) (v:a) (j:seq_index (filter f s))
  : Lemma (requires (f v = f (index s i) /\ filter_index_map f s j <> i))
          (ensures (index (filter f s) j = index (filter f (upd s i v)) j))
  = lemma_filter_update_index_neq_aux f s i v j
*)

let rec lemma_filter_extensionality_aux (#a:Type) (f1 f2:a -> bool) (s:seq a):
  Lemma (requires (ext_pred f1 f2))
        (ensures (filter f1 s == filter f2 s))
        (decreases (length s)) =
  let n = length s in
  if n = 0 then ()
  else lemma_filter_extensionality_aux f1 f2 (prefix s (n - 1))

let lemma_filter_extensionality = lemma_filter_extensionality_aux

let rec lemma_filter_conj_aux (#a:Type) (f1 f2: a -> bool) (s:seq a):
  Lemma (requires True)
        (ensures (filter (conj f1 f2) s == filter f1 (filter f2 s)))
        (decreases (length s)) =
  let n = length s in
  if n = 0 then ()
  else (
    let s' = prefix s (n - 1) in
    let e = index s (n - 1) in
    lemma_filter_conj_aux f1 f2 s';
    if conj f1 f2 e then (
      lemma_filter_extend2 (conj f1 f2) s;
      lemma_filter_extend2 f2 s;
      let s2' = filter f2 s' in
      let s2 = append1 s2' e in
      lemma_prefix_append s2' (create 1 e);
      lemma_filter_extend2 f1 s2
    )
    else if not (f2 e) then (
      lemma_filter_extend1 (conj f1 f2) s;
      lemma_filter_extend1 f2 s
    )
    else (
      lemma_filter_extend1 (conj f1 f2) s;
      lemma_filter_extend2 f2 s;
      let s2' = filter f2 s' in
      let s2 = append1 s2' e in
      lemma_prefix_append s2' (create 1 e);
      lemma_filter_extend1 f1 s2
    )
  )

let lemma_filter_conj = lemma_filter_conj_aux

let lemma_filter_comm (#a:Type) (f1 f2:a -> bool) (s:seq a):
  Lemma (filter f2 (filter f1 s) == filter f1 (filter f2 s)) =
  let cf12 = conj f1 f2 in
  let cf21 = conj f2 f1 in
  assert(ext_pred cf12 cf21);
  lemma_filter_extensionality cf12 cf21 s;
  lemma_filter_conj f1 f2 s;
  lemma_filter_conj f2 f1 s

let last_index_opt (#a:Type) (f:a -> bool) (s:seq a):
  Tot (option (i:seq_index s{f (index s i)})) =
  let fs = filter f s in
  if length fs = 0 then None
  else Some (filter_index_map f s ((length fs) - 1))

let lemma_last_index_correct1 (#a:Type) (f:a -> bool) (s:seq a) (i:seq_index s):
  Lemma (requires (exists_sat_elems f s /\ i > last_index f s))
        (ensures (not (f (index s i)))) =
  let j = last_index f s in
  if f (index s i) then
    lemma_filter_index_inv_map_monotonic f s j i
  else ()

let lemma_last_index_correct2 (#a:Type) (f:a -> bool)  (s:seq a) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (exists_sat_elems f s /\ last_index f s >= i)) =
  let n = length s in
  let ri = filter_index_inv_map f s i in
  assert (exists_sat_elems f s);
  let j = last_index f s in
  if j < i then
    lemma_filter_index_inv_map_monotonic f s j i
  else ()

let last_index_opt_elim (#a:Type) (f:a → bool) (s:seq a)
  : Lemma (match last_index_opt f s with
           | None → ∀ (i:seq_index s). not (f (Seq.index s i))
           | Some i → f (Seq.index s i) ∧ (∀ (j:seq_index s). j > i ⟹ not (f (Seq.index s j)))) =
  match last_index_opt f s with
  | None → lemma_filter_all_not f s
  | Some i → assert (f (index s i)); 
             let aux (j:seq_index s{j > i}): 
               Lemma (not (f (index s j))) = 
               lemma_last_index_correct1 f s j in   
             FStar.Classical.forall_intro aux

let lemma_last_index_prefix (#a:Type) (f:a -> bool) (s:seq a) (i:nat{i <= length s}):
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

let lemma_not_exists_prefix (#a:Type) (f:a -> bool) (s:seq a) (i:nat{i <= length s}):
  Lemma (requires (not (exists_sat_elems f s)))
        (ensures (not (exists_sat_elems f (prefix s i)))) =
  let s' = prefix s i in
  if exists_sat_elems f s' then (
    let li' = last_index f s' in
    lemma_prefix_index s i li';
    lemma_last_index_correct2 f s li'
  )
  else ()

let lemma_exists_sat_elems_exists (#a:Type) (f:a → bool) (s:seq a)
  : Lemma (exists_sat_elems f s <==> (∃ (i:seq_index s). f (Seq.index s i)))
  = if length (filter f s) = 0 
    then lemma_filter_all_not f s 

let lemma_exists_prefix_implies_exists (#a:Type) (f:a -> bool) (s:seq a) (i:nat{i <= length s}):
  Lemma (requires (exists_sat_elems f (prefix s i)))
        (ensures (exists_sat_elems f s)) =
  let s' = prefix s i in
  let li = last_index f s' in
  lemma_last_index_correct2 f s li

let lemma_last_index_last_elem_nsat (#a:Type) (f:a -> bool) (s:seq a{length s > 0}):
  Lemma (requires (not (f (index s (length s - 1)))))
        (ensures ((exists_sat_elems f s ==> last_index f s < length s - 1) /\
                  exists_sat_elems f s = exists_sat_elems f (prefix s (length s - 1)))) =
  if exists_sat_elems f s then
    let li = last_index f s in
    ()
  else ()

let lemma_last_index_opt_last_elem_nsat (#a:Type) (f:a -> bool) (s:seq a{length s > 0}):
  Lemma (requires (not (f (index s (length s - 1)))))
        (ensures (match last_index_opt f s, last_index_opt f (prefix s (length s - 1)) with
                  | None, None -> True
                  | Some v0, Some v1 -> v0 == v1
                  | _ -> False))
  = lemma_last_index_last_elem_nsat f s

let lemma_last_index_last_elem_sat (#a:Type) (f:a -> bool) (s:seq a{length s > 0}):
  Lemma (requires (f (index s (length s - 1))))
        (ensures (exists_sat_elems f s /\ last_index f s = length s - 1)) =
  let n = length s in
  lemma_last_index_correct2 f s (n - 1)

let lemma_exists_sat_elems_extensionality (#a:Type) (f1 f2:a -> bool) (s: seq a):
  Lemma (requires (ext_pred f1 f2))
        (ensures (exists_sat_elems f1 s = exists_sat_elems f2 s))
        (decreases (length s)) =
  if exists_sat_elems f1 s then
    let i = last_index f1 s in
    lemma_last_index_correct2 f2 s i
  else if exists_sat_elems f2 s then
    let i = last_index f2 s in
    lemma_last_index_correct2 f1 s i
  else ()

let lemma_last_index_extensionality (#a:Type) (f1 f2:a -> bool) (s: seq a{exists_sat_elems f1 s}):
  Lemma (requires (ext_pred f1 f2))
        (ensures (exists_sat_elems f2 s /\
                  last_index f1 s = last_index f2 s)) =
  lemma_exists_sat_elems_extensionality f1 f2 s;
  let i1 = last_index f1 s in
  let i2 = last_index f2 s in
  lemma_last_index_correct2 f2 s i1;
  lemma_last_index_correct2 f1 s i2

let lemma_exists_sat_conj (#a:Type) (f1 f2: a -> bool) (s: seq a):
  Lemma(requires True)
       (ensures (exists_sat_elems (conj f1 f2) s = exists_sat_elems f1 (filter f2 s)))
       [SMTPat (exists_sat_elems (conj f1 f2) s)] =
  let s2 = filter f2 s in
  if exists_sat_elems (conj f1 f2) s then
    let i = last_index (conj f1 f2) s in
    let j = filter_index_inv_map f2 s i in
    lemma_last_index_correct2 f1 s2 j
  else if exists_sat_elems f1 s2 then
    let j = last_index f1 s2 in
    let i = filter_index_map f2 s j in
    lemma_last_index_correct2 (conj f1 f2) s i
  else ()

let lemma_last_idx_conj (#a:Type) (f1 f2: a -> bool)
                        (s: seq a{exists_sat_elems (conj f1 f2) s}):
  Lemma (last_index (conj f1 f2) s = filter_index_map f2 s (last_index f1 (filter f2 s))) =
  let s2 = filter f2 s in
  let i = last_index (conj f1 f2) s in
  let j = filter_index_inv_map f2 s i in
  lemma_filter_maps_correct f2 s i;
  lemma_last_index_correct2 f1 s2 j;
  let j' = last_index f1 s2 in
  if j' = j then ()
  else
    let i' = filter_index_map f2 s j' in
    lemma_last_index_correct2 (conj f1 f2) s i';
    lemma_filter_index_map_monotonic f2 s j j'

let first_index (#a:Type) (f:a -> bool) (s:seq a{exists_sat_elems f s})
  : Tot (i:seq_index s{f (index s i)}) =
  filter_index_map f s 0

let lemma_first_index_correct1 (#a:Type) (f:a -> bool) (s:seq a) (i:seq_index s):
  Lemma (requires (exists_sat_elems f s /\ i < first_index f s))
        (ensures (not (f (index s i)))) =
  let fi = first_index f s in
  if f (index s i) then
    lemma_filter_index_inv_map_monotonic f s i fi
  else ()

let lemma_first_index_correct2 (#a:Type) (f:a -> bool) (s:seq a) (i:seq_index s):
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

let lemma_map_prefix (#a #b: Type) (f:a -> b) (s:seq a) (i: seq_index s):
  Lemma (requires True)
        (ensures (map f (prefix s i) == prefix (map f s) i)) =
  let mp = map f (prefix s i) in
  let pm = prefix (map f s) i in
  assert(equal mp pm);
  ()

let lemma_map_suffix (#a #b: Type) (f:a -> b) (s:seq a) (i:nat{i <= length s}):
  Lemma (requires True)
        (ensures (map f (suffix s i) == suffix (map f s) i)) =
  let ms = map f (suffix s i) in
  let sm = suffix (map f s) i in
  assert(equal ms sm);
  ()

let lemma_map_extend (#a #b:Type) (f:a -> b) (s:seq a{length s > 0}):
  Lemma (map f s == append1 (map f (prefix s (length s - 1)))
                            (f (index s (length s - 1)))) = 
  assert(equal (map f s) (append1 (map f (prefix s (length s - 1)))
                            (f (index s (length s - 1)))));
  ()

let rec zip_aux (#a #b: Type) (sa: seq a) (sb: seq b{length sb = length sa}):
  Tot (sab: (seq (a * b)){length sab = length sa})
  (decreases (length sa)) =
  let n = length sa in
  if n = 0 then empty
  else
    let sa' = prefix sa (n - 1) in
    let sb' = prefix sb (n - 1) in
    append1 (zip_aux sa' sb') (index sa (n - 1), index sb (n - 1))

let zip = zip_aux

let rec lemma_zip_index_aux (#a #b: Type) (sa: seq a) (sb: seq b{length sa = length sb}) (i:seq_index sa):
  Lemma (requires (True))
        (ensures (fst (index (zip sa sb) i) == index sa i /\
                  snd (index (zip sa sb) i) == index sb i))
        (decreases (length sa)) =
  let n = length sa in
  if n = 0 then ()
  else if i = n - 1 then ()
  else
    let sa' = prefix sa (n - 1) in
    let sb' = prefix sb (n - 1) in
    lemma_zip_index_aux sa' sb' i

let lemma_zip_index = lemma_zip_index_aux

let rec unzip_aux (#a #b: Type) (sab: seq (a * b)):
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

let rec lemma_unzip_index_aux (#a #b: Type) (sab: seq (a * b)) (i:seq_index sab):
  Lemma (requires (True))
        (ensures (fst (index sab i) == index (fst (unzip sab)) i /\
                  snd (index sab i) == index (snd (unzip sab)) i))
        (decreases (length sab)) =
  let n = length sab in
  if n = 0 then ()
  else if i = n - 1 then ()
  else
    let sab' = prefix sab (n - 1) in
    lemma_unzip_index_aux sab' i

let lemma_unzip_index = lemma_unzip_index_aux

let lemma_zip_unzip (#a #b: Type) (sa: seq a) (sb: seq b{length sb = length sa}):
  Lemma (requires (True))
        (ensures ((sa, sb) == unzip (zip sa sb))) =
  let sab = zip sa sb in
  assert(length sa = length (fst (unzip sab)));
  let aux1 (i:seq_index sa):
    Lemma (requires (True))
          (ensures (index sa i == index (fst (unzip sab)) i))
          [SMTPat (index sa i)] =
    lemma_unzip_index sab i;
    lemma_zip_index sa sb i
  in
  assert(equal sa (fst (unzip sab)));
  let aux2 (i:seq_index sb):
    Lemma (requires (True))
          (ensures (index sb i == index (snd (unzip sab)) i))
          [SMTPat (index sb i)] =
    lemma_unzip_index sab i;
    lemma_zip_index sa sb i
  in
  assert(equal sb (snd (unzip sab)));
  ()

let lemma_unzip_extend (#a #b: Type) (sab: seq (a * b){length sab > 0}):
  Lemma (requires True)
        (ensures (fst (unzip sab) == append1 (fst (unzip (hprefix sab))) (fst (telem sab)) /\
                  snd (unzip sab) == append1 (snd (unzip (hprefix sab))) (snd (telem sab)))) = ()

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

let lemma_reduce_empty (#a:Type) (#b:Type) (b0:b) (f:a -> b -> b):
  Lemma (reduce b0 f (empty #a) == b0) = ()

let rec lemma_reduce_prefix_aux (#a:Type) (#b:Type)
                                (b0: b) (f: a -> b -> b) (s: seq a)
                                (i:nat{i <= length s}):
  Lemma (requires True)
        (ensures (reduce b0 f s == reduce (reduce b0 f (prefix s i)) f (suffix s (length s - i))))
        (decreases (length s)) =
  let n = length s in
  if n = 0 then ()
  else if i = n then ()
  else lemma_reduce_prefix_aux b0 f (prefix s (n - 1)) i

let lemma_reduce_prefix = lemma_reduce_prefix_aux

let rec lemma_reduce_property_closure_seq_mem (#a:Type) (#b:Type)
  (p:b -> Type0)
  (b0:b)
  (f:a -> b -> b)
  (s:seq a)
  : Lemma
      (requires
        p b0 /\
        (forall (n:seq_index s) (y:b). p y ==> p (f (index s n) y)))
      (ensures p (reduce b0 f s))
      (decreases length s)
  = if length s = 0 then ()
    else lemma_reduce_property_closure_seq_mem p b0 f (prefix s (length s - 1))

let lemma_reduce_identity (#a:Type) (#b:Type) (b0: b) (f: a -> b -> b) (s: seq a):
  Lemma (requires (forall (x:a). f x b0 == b0))
        (ensures (reduce b0 f s == b0)) =
  lemma_reduce_property_closure_ty (fun y -> y == b0) b0 f s

let lemma_reduce_singleton (#a:Type) (#b:Type) (b0: b) (f: a -> b -> b) (s: seq a{length s = 1}):
  Lemma (reduce b0 f s == f (index s 0) b0) = ()

let lemma_reduce_append (#a:Type) (#b:Type) (b0:b) (f: a -> b -> b) (s: seq a) (x:a):
  Lemma (reduce b0 f (append1 s x) == f x (reduce b0 f s)) =
  lemma_prefix_append s (create 1 x)

let lemma_reduce_append2 (#a:Type) (#b:Type) (b0:b) (f: a -> b -> b) (s: seq a{length s > 0}):
  Lemma (reduce b0 f s == f (index s (length s - 1)) (reduce b0 f (prefix s (length s - 1)))) = ()

(* The index of the next entry that satisfies a filter predicate *)
open FStar.Calc
let next_index_opt (#a:Type) (f:a → bool) (s:seq a) (i:seq_index s):
  Tot (option (j:seq_index s{j > i && f (index s j)})) = 
  let n = length s in
  (* get the subseq after index i *)
  let s' = suffix s (n - (i + 1)) in
  let fs' = filter f s' in
  if length fs' = 0 then None
  else (
    //See https://github.com/FStarLang/FStar/wiki/Calculational-proofs
    calc (==) {
      (index s' (first_index f s'));
      (==) {  lemma_suffix_index s (n - (i + 1)) (first_index f s') }
      (index s (n - (n - (i + 1)) + first_index f s'));
      (==) { }
      (index s (i + 1 + first_index f s'));
    };
    Some (i + 1 + first_index f s')
  )

let intro_has_next (#a:Type) (f:a → bool) (s:seq a) (i:seq_index s) (k:seq_index s{i < k ∧ f (Seq.index s k)})
  : Lemma (has_next f s i /\
           Some?.v (next_index_opt f s i) <= k)
  = let n = length s in
    let s' = suffix s (n - (i + 1)) in
    assert (f (index s' (k - (i + 1)))); 
    lemma_filter_exists f s';
    lemma_first_index_correct2 f s' (k - (i + 1))

let prev_index_opt (#a:Type) (f:a → bool) (s:seq a) (i:seq_index s):
  Tot (option (j:seq_index s{j < i && f (index s j)})) =
  let s' = prefix s i in
  let fs' = filter f s' in
  if length fs' = 0 then None
  else Some (last_index f s')

let filter_snoc (#a:Type) (f:a -> bool) (s:seq a) (x:a)
  : Lemma (if f x 
           then filter f (Seq.snoc s x) `Seq.equal` Seq.snoc (filter f s) x
           else filter f (Seq.snoc s x) `Seq.equal` filter f s)
  = assert (Seq.equal (prefix (Seq.snoc s x) (Seq.length s)) s)


let filter_map_emp (#a:Type) (#b:Type) (filter: a -> bool) (f:refine filter -> b) 
  : Lemma (filter_map filter f Seq.empty `Seq.equal` Seq.empty)
  = ()

let map_upd (#a #b:Type) (f:a -> b) (s:seq a) (i:seq_index s) (x:a)
  : Lemma (map f (Seq.upd s i x) `Seq.equal` Seq.upd (map f s) i (f x))
  = ()

(* the element at each index is a member of the seqeunce *)
let each_index_mem (#a: eqtype) (l: seq a) (i: seq_index l)
  : Lemma (ensures (mem (index l i) l))
  = ()

let rec find_dupl_idx (#a: eqtype) (s: seq a)
  : Tot (o: option (nat * nat) { (None = o <==> distinct_elems s) /\
                               (Some? o ==>
                               (let i,j = Some?.v o in
                                i < length s /\ j < length s /\
                                i <> j /\ index s i = index s j))})
    (decreases (length s))
  = if length s = 0 then None
    else (
      let i = length s - 1 in
      let s' = prefix s i in
      let x = index s i in
      let os' = find_dupl_idx s' in

      if Some? os' then (
        let i,j = Some?.v os' in
        let f: squash (index s' i = index s' j /\ i <> j) = () in
        introduce exists i1 i2. index s i1 = index s i2 /\ i1 <> i2 with i j and f;
        assert(~(distinct_elems s));
        Some (i,j)
      )
      else (
        assert(distinct_elems s');

        if mem x s' then (
          let j = index_mem x s' in
          let f: squash (index s i = index s j /\ i <> j) = () in
          introduce exists i1 i2. index s i1 = index s i2 /\ i1 <> i2 with i j and f;
          assert(~(distinct_elems s));
          Some (i,j)
        )
        else (
          let aux (i1 i2:_)
            : Lemma (ensures (i1 <> i2 ==> index s i1 <> index s i2))
            = if i1 <> i2 && index s i1 = index s i2 then (
                 if i1 = i then
                   each_index_mem s' i2
                 else if i2 = i then
                   each_index_mem s' i1
                 else (
                   let f: squash (index s' i1 = index s' i2 /\ i1 <> i2) = () in
                   introduce exists i1 i2. index s' i1 = index s' i2 /\ i1 <> i2 with i1 i2 and f;
                   assert(~(distinct_elems s'));
                   ()
                 )
              )
          in
          introduce forall i1 i2. (i1 <> i2 ==> index s i1 <> index s i2) with aux i1 i2;
          None
        )
      )
    )

let distinct_elems_comp (#a: eqtype) (s: seq a)
  : Tot (b:bool {b <==> distinct_elems s})
  = None = find_dupl_idx s

let lemma_elem_idx_uniq (#a: eqtype) (s: seq a{distinct_elems s}) (i: seq_index s)
  : Lemma (ensures (let e = index s i in
                    index_mem e s = i))
  = ()
