module Zeta.MultiSet

open FStar.List.Tot


/// We represet a multiset with a sorted associative list
///   where the second component of each list element is the
///   cardinality of the first component in the set
///
/// The list is sorted on the first component of its elements


let rec sorted (#a:eqtype) (f:cmp a) (l:list (a & pos)) : Type0 =
  match l with
  | [] -> True
  | [_] -> True
  | (x, _)::(y, card_y)::tl ->
    f x y /\
    x =!= y /\
    sorted f ((y, card_y)::tl)

let mset a f = l:list (a & pos){sorted f l}


/// We will use this function, rather than pattern matching to get better implicit inference

let tl (#a:eqtype) (#f:cmp a) (s:mset a f{Cons? s}) : mset a f = tl s

let empty #_ #_ = []

let create #_ #_ x m = [x, m]

let rec mem #_ #_ x s =
  match s with
  | [] -> 0
  | (y, n)::_ -> if x = y then n else mem x (tl s)


let mem_empty (#a: eqtype) (f: cmp a) (x:a)
  : Lemma (mem x (empty #_ #f) == 0)
  = ()

/// We define an auxiliary add function that
///   maintains some invariants on the returned multiset,
///   so as to typecheck the body (the recursive call case)

private let rec add (#a:eqtype) (#f:cmp a) (s:mset a f) (x:a)
  : s':mset a f{
      Cons? s' /\
      (fst (hd s') == x \/ (Cons? s /\ fst (hd s') == fst (hd s)))}
  = match s with
    | [] -> [x, 1]
    | (y, n)::_ ->
      if x = y then (y, n + 1)::(tl s)
      else if f x y then (x, 1)::s
      else (y, n)::(add (tl s) x)

let add_elem = add

let rec seq2mset_aux (#a:eqtype) (#f:cmp a) (s:Seq.seq a)
  : Tot (mset a f) (decreases (Seq.length s))
  = if Seq.length s = 0 then empty
    else
      let ms = seq2mset_aux (Seq.tail s) in
      add_elem ms (Seq.index s 0)

let seq2mset = seq2mset_aux

let zero_length_implies_empty (#a:eqtype) (#f: cmp a) (s: Seq.seq a)
  : Lemma (ensures (Seq.length s = 0 ==> seq2mset #a #f s == empty))
  = ()

/// Again defining an auxiliary function to maintain some invariants on the return type

let rec union_aux (#a:eqtype) (#f:cmp a) (s1 s2:mset a f) :
  s:mset a f{
    ((Cons? s1 /\ Cons? s2) ==>
     (Cons? s /\ (let x1 = fst (hd s1) in
                 let x2 = fst (hd s2) in
                 if f x1 x2 then fst (hd s) == x1
                 else fst (hd s) == x2))) /\
    (Nil? s1 ==> s == s2) /\
    (Nil? s2 ==> s == s1)} =
  match s1, s2 with
  | [], _ -> s2
  | _, [] -> s1
  | (x1, n1)::_, (x2, n2)::_ ->
    if x1 = x2
    then (x1, n1 + n2)::(union_aux (tl s1) (tl s2))
    else if f x1 x2
    then (x1, n1)::(union_aux (tl s1) s2)
    else (x2, n2)::(union_aux s1 (tl s2))

let union = union_aux

let rec size #_ #_ s =
  match s with
  | [] -> 0
  | (_, n)::_ -> n + size (tl s)


/// A helper lemma saying that
///   an element that is less than (per f) the hd of the mset, is not in the mset

private let rec mem_elt_lt_hd (#a:eqtype) (#f:cmp a) (x:a) (s:mset a f{Cons? s})
  : Lemma
      (requires f x (fst (hd s)) /\ x <> fst (hd s))
      (ensures mem x s == 0)
  = match s with
    | [_] -> ()
    | _ -> mem_elt_lt_hd x (tl s)


/// A corollary of mem_elt_lt_hd, that hd of an mset is not present in the tl

private let mem_hd_in_tl (#a:eqtype) (#f:cmp a) (s:mset a f{Cons? s})
  : Lemma
      (requires True)
      (ensures mem (fst (hd s)) (tl s) == 0)
  = match s with
    | [_] -> ()
    | (x, _)::_ -> mem_elt_lt_hd x (tl s)

let rec diff_elem #a #f s1 s2 =
  match s1, s2 with
  | (x, _)::_, [] -> x
  | (x1, n1)::_, (x2, n2)::_ ->
    if x1 = x2
    then (if n1 > n2 then x1
          else (mem_hd_in_tl s1; diff_elem (tl s1) (tl s2)))
    else if f x1 x2 then (mem_elt_lt_hd x1 s2; x1)
    else (mem_elt_lt_hd x2 s1; diff_elem s1 (tl s2))


private let rec add_mem (#a:eqtype) (#f:cmp a) (x:a) (s:mset a f)
  : Lemma (mem x (add_elem s x) == mem x s + 1)
  = match s with
    | [] -> ()
    | (y, _)::_ ->
      if x = y then ()
      else if f x y then mem_elt_lt_hd x s
      else add_mem x (tl s)

private let rec add_mem_neq (#a:eqtype) (#f:cmp a)
  (x:a)
  (s:mset a f)
  (y:a{x =!= y})
  : Lemma (mem y (add_elem s x) == mem y s)
  = match s with
    | [] -> ()
    | (z, _)::_ ->
      if x = z then ()
      else if f x z then ()
      else add_mem_neq #a #f x (tl s) y


private let rec index_of_mselem_aux (#a:eqtype) (#f:cmp a)
  (s:Seq.seq a)
  (x:a{seq2mset #a #f s `contains` x})
  : Tot (i:seq_index s{Seq.index s i == x}) (decreases (Seq.length s))
  = if Seq.index s 0 = x then 0
    else begin
      add_mem_neq (Seq.index s 0) (seq2mset #a #f (Seq.tail s)) x;
      1 + index_of_mselem_aux #a #f (Seq.tail s) x
    end

let index_of_mselem = index_of_mselem_aux

let equal #a #f s1 s2 = s1 == s2

private let forall_x_mem_in_tl (#a:eqtype) (#f:cmp a) (s1 s2:mset a f)
  : Lemma
      (requires
        (forall (x:a). mem x s1 == mem x s2) /\
        Cons? s1 /\ Cons? s2)
      (ensures
        forall (x:a). mem x (tl s1) == mem x (tl s2))
  = let aux (x:a)
      : Lemma (mem x (tl s1) == mem x (tl s2))
      = match s1, s2 with
        | (x1, _)::_, (x2, _)::_ ->
          if x1 = x2 then begin
            if x1 = x then (mem_hd_in_tl s1; mem_hd_in_tl s2)
          end
          else if f x1 x2 then mem_elt_lt_hd x1 s2
          else mem_elt_lt_hd x2 s1
    in
    Classical.forall_intro aux

let rec eq_intro #_ #f s1 s2 =
  match s1, s2 with
  | [], [] -> ()
  | (_, _)::_, [] -> ()
  | [], (_, _)::_ -> ()
  | (x, n_x)::_, (y, n_y)::_ ->
    if x = y then (forall_x_mem_in_tl s1 s2; eq_intro (tl s1) (tl s2))
    else if f x y then mem_elt_lt_hd x s2
    else mem_elt_lt_hd y s1

let eq_refl #_ #_ _ _ = ()

let eq_elim #_ #_ _ _ = ()

let not_eq #_ #_ _ _ _ = ()

private let rec seq2mset_mem_aux (#a:eqtype) (#f:cmp a) (s:Seq.seq a) (x:a)
  : Lemma
      (ensures Seq.count x s == mem x (seq2mset #a #f s))
      (decreases (Seq.length s))
  = if Seq.length s = 0 then ()
    else begin
      let s_hd = Seq.index s 0 in
      let s_tl = Seq.tail s in
      seq2mset_mem_aux #a #f s_tl x;
      let mset_tl = seq2mset #a #f s_tl in
      if s_hd = x
      then add_mem x mset_tl
      else add_mem_neq s_hd mset_tl x
    end

let seq2mset_mem = seq2mset_mem_aux

private let rec seq_count_i (#a:eqtype) (s:Seq.seq a) (i:seq_index s)
  : Lemma
      (ensures Seq.count (Seq.index s i) s > 0)
      (decreases (Seq.length s))
  = if i = 0 then ()
    else seq_count_i (Seq.tail s) (i - 1)

let mset_contains_seq_element #a #f s i =
  seq_count_i s i;
  seq2mset_mem #a #f s (Seq.index s i)

private let rec union_mem_aux (#a:eqtype) (#f:cmp a) (s1 s2:mset a f) (x:a)
  : Lemma (mem x (union s1 s2) == mem x s1 + mem x s2)
  = match s1, s2 with
    | [], _ -> ()
    | _, [] -> ()
    | (x1, n1)::_, (x2, n2)::_ ->
      if x1 = x2
      then union_mem_aux (tl s1) (tl s2) x
      else if f x1 x2
      then begin
        union_mem_aux (tl s1) s2 x;
        if x = x1
        then mem_elt_lt_hd x s2
        else if f x x1
        then (mem_elt_lt_hd x s1; mem_elt_lt_hd x s2)
      end
      else begin
        union_mem_aux s1 (tl s2) x;
        if x = x2
        then mem_elt_lt_hd x s1
        else if f x x2
        then (mem_elt_lt_hd x s2; mem_elt_lt_hd x s1)
      end

private let eq_intro_aux (#a:eqtype) (#f:cmp a) (s1 s2:mset a f)
  : Lemma
      (requires forall (x:a). mem x s1 == mem x s2)
      (ensures s1 == s2)
  = eq_intro s1 s2; eq_elim s1 s2

let seq_append_mset #a #f s1 s2 =
  let ms1 = seq2mset #a #f s1 in
  let ms2 = seq2mset #a #f s2 in
  let ms = seq2mset #a #f (Seq.append s1 s2) in
  Seq.lemma_append_count s1 s2;
  Classical.forall_intro (seq2mset_mem #a #f s1);
  Classical.forall_intro (seq2mset_mem #a #f s2);    
  Classical.forall_intro (seq2mset_mem #a #f (Seq.append s1 s2));
  Classical.forall_intro (union_mem_aux ms1 ms2);
  eq_intro_aux ms (union ms1 ms2)

let rec seq_count_create (#a:eqtype) (n:nat) (x:a)
  : Lemma (Seq.count x (Seq.create n x) == n /\
           (forall y. y =!= x ==> Seq.count y (Seq.create n x) == 0))
  = if n = 0 then ()
    else begin
      assert (Seq.equal (Seq.tail (Seq.create n x))
                        (Seq.create (n-1) x));

      assert (Seq.count x (Seq.create n x) == 1 + Seq.count x (Seq.tail (Seq.create n x)));
      seq_count_create (n-1) x
    end

let seq2mset_add_elem #a #f s x =
  add_mem x (seq2mset #a #f s);
  Classical.forall_intro (add_mem_neq x (seq2mset #a #f s));

  assert (forall y. (y == x ==>
                mem y (add_elem (seq2mset #a #f s) x) == mem y (seq2mset #a #f s) + 1) /\
               (y =!= x ==>
                mem y (add_elem (seq2mset #a #f s) x) == mem y (seq2mset #a #f s)));


  Classical.forall_intro (seq2mset_mem #a #f (append1 s x));

  assert (forall y. mem y (seq2mset #a #f (append1 s x)) ==
               Seq.count y (append1 s x));

  Seq.lemma_append_count s (Seq.create 1 x);

  assert (forall y. Seq.count y (append1 s x) ==
               Seq.count y s + Seq.count y (Seq.create 1 x));

  seq_count_create 1 x;

  assert (forall y. (y == x ==>
                Seq.count y (append1 s x) == Seq.count y s + 1) /\
               (y =!= x ==>
                Seq.count y (append1 s x) == Seq.count y s));

  Classical.forall_intro (seq2mset_mem #a #f s);

  assert (forall y. Seq.count y s == mem y (seq2mset #a #f s));

  assert (forall y. mem y (add_elem (seq2mset #a #f s) x) ==
               Seq.count y (append1 s x));
  eq_intro_aux (seq2mset #a #f (append1 s x)) (add_elem (seq2mset #a #f s) x)

let seq_prefix_mset_mem #a #f s s' x =
  let is_prefix_tail (#a:eqtype) (s1 s2:Seq.seq a)
  : Lemma
      (requires is_prefix s1 s2)
      (ensures Seq.length s2 == 0 \/ is_prefix (Seq.tail s1) (Seq.tail s2))
  = if Seq.length s2 = 0 then ()
    else begin  
      prefix_slice s1 (Seq.length s2);
      prefix_slice (Seq.tail s1) (Seq.length s2 - 1)
    end
  in
  let rec aux (s1 s2:Seq.seq a) (x:a)
    : Lemma
        (requires is_prefix s1 s2)
        (ensures Seq.count x s2 <= Seq.count x s1)
        (decreases (Seq.length s1))
    = if Seq.length s2 = 0 then ()
      else begin
        is_prefix_tail s1 s2;
        aux (Seq.tail s1) (Seq.tail s2) x
      end
  in
  aux s s' x;
  seq2mset_mem #a #f s x;
  seq2mset_mem #a #f s' x


let seq_mset_elem2 #a #f s i1 i2 =
  let rec aux (s:Seq.seq a) (i1 i2:seq_index s)
    : Lemma
        (requires i1 =!= i2 /\ Seq.index s i1 == Seq.index s i2)
        (ensures Seq.count (Seq.index s i1) s >= 2)
        (decreases (Seq.length s))
    = if i1 = 0 then seq_count_i (Seq.tail s) (i2 - 1)
      else if i2 = 0 then seq_count_i (Seq.tail s) (i1 - 1)
      else aux (Seq.tail s) (i1 - 1) (i2 - 1)
    in
    aux s i1 i2;
    seq2mset_mem #a #f s (Seq.index s i1)


/// Proof for bijection_seq_mset
///   We will prove it by induction,
///   exhibiting a bijection for the two sequences after removing 0th and (f 0)th elements

/// Perhaps move to FStar.Seq?

private let seq_remove (#a:eqtype) (s:Seq.seq a) (i:seq_index s)
  : Seq.seq a
  = Seq.append (Seq.slice s 0 i) (Seq.slice s (i + 1) (Seq.length s))

#push-options "--z3rlimit_factor 7"
private let seq_remove_count1 (#a:eqtype) (s:Seq.seq a) (i:seq_index s)
  : Lemma
      (Seq.count (Seq.index s i) s == Seq.count (Seq.index s i) (seq_remove s i) + 1)
  = let x = Seq.index s i in
    Seq.lemma_count_slice s i;
    assert (Seq.count x s ==
            Seq.count x (Seq.slice s 0 i) + Seq.count x (Seq.slice s i (Seq.length s)));
    let s1 = Seq.slice s i (Seq.length s) in
    if Seq.length s1 = 0 then ()
    else begin
      assert (Seq.count x s1 ==
              (if Seq.index s1 0 = x then 1 + Seq.count x (Seq.tail s1)
               else Seq.count x (Seq.tail s1)));
      assert (Seq.index s1 0 == Seq.index s i);
      assert (Seq.count x s1 == 1 + Seq.count x (Seq.tail s1));
      assert (Seq.equal (Seq.tail s1)
                        (Seq.slice s (i + 1) (Seq.length s)));
      assert (Seq.count x s1 == 1 + Seq.count x (Seq.slice s (i + 1) (Seq.length s)));
      assert (Seq.count x s ==
              Seq.count x (Seq.slice s 0 i) + Seq.count x (Seq.slice s (i + 1) (Seq.length s)) + 1);
      Seq.lemma_append_count (Seq.slice s 0 i) (Seq.slice s (i + 1) (Seq.length s))
    end
#pop-options

#push-options "--fuel 1 --ifuel 0"
private let seq_remove_count2 (#a:eqtype)
  (s:Seq.seq a)
  (i:seq_index s)
  (y:a{y =!= Seq.index s i})
  : Lemma (Seq.count y s == Seq.count y (seq_remove s i))
  = Seq.lemma_count_slice s i;
    assert (Seq.count y s ==
            Seq.count y (Seq.slice s 0 i) + Seq.count y (Seq.slice s i (Seq.length s)));
    let s1 = Seq.slice s i (Seq.length s) in
    if Seq.length s1 = 0 then ()
    else begin
      assert (Seq.count y s1 ==
              (if Seq.index s1 0 = y then 1 + Seq.count y (Seq.tail s1)
               else Seq.count y (Seq.tail s1)));
      assert (Seq.index s1 0 == Seq.index s i);
      assert (Seq.count y s1 == Seq.count y (Seq.tail s1));
      Seq.lemma_append_count (Seq.slice s 0 i) (Seq.slice s (i + 1) (Seq.length s))
    end
#pop-options

/// This is the bijection for the recursive call
#push-options "--z3rlimit_factor 3"
private let ismap_next (#a:eqtype)
  (s1:Seq.seq a{Seq.length s1 > 0})
  (s2:Seq.seq a)
  (f:into_smap s1 s2)
  : into_smap (Seq.slice s1 1 (Seq.length s1))
              (seq_remove s2 (f 0))
  = let s1' = Seq.slice s1 1 (Seq.length s1) in
    let s2' = seq_remove s2 (f 0) in
    let f : seq_index s1' -> seq_index s2' = fun i ->
      let n = f (i + 1) in
      if n < f 0 then n
      else n - 1 in

    f
#pop-options

private let rec seq_count_into_smap_x (#a:eqtype)
  (s1 s2:Seq.seq a)
  (f:into_smap s1 s2)
  (x:a)
  : Lemma
      (ensures Seq.count x s1 <= Seq.count x s2)
      (decreases (Seq.length s1))      
  = if Seq.length s1 = 0 then ()
    else begin
      let s1' = Seq.slice s1 1 (Seq.length s1) in
      let s2' = seq_remove s2 (f 0) in
      seq_count_into_smap_x s1' s2' (ismap_next s1 s2 f) x;
      assert (Seq.count x s1' <= Seq.count x s2');
      if x = Seq.index s1 0 then seq_remove_count1 s2 (f 0)
      else seq_remove_count2 s2 (f 0) x
    end

private let seq_count_into_smap (#a:eqtype) (s1 s2:Seq.seq a) (f:into_smap s1 s2)
  : Lemma (forall (x:a). Seq.count x s1 <= Seq.count x s2)
  = let aux (x:a) : Lemma (Seq.count x s1 <= Seq.count x s2)
      = seq_count_into_smap_x s1 s2 f x
    in
    Classical.forall_intro aux

let bijection_seq_mset #a #f s1 s2 f12 f21 =
  seq_count_into_smap s1 s2 f12;
  seq_count_into_smap s2 s1 f21;
  Classical.forall_intro (seq2mset_mem #a #f s1);
  Classical.forall_intro (seq2mset_mem #a #f s2);
  eq_intro_aux (seq2mset #a #f s1) (seq2mset #a #f s2)

let union_mem = union_mem_aux

let union_comm #_ #_ s1 s2 =
  Classical.forall_intro (union_mem_aux s1 s2);
  Classical.forall_intro (union_mem_aux s2 s1);
  eq_intro_aux (union s1 s2) (union s2 s1)

#push-options "--fuel 0 --fuel 0"
let union_assoc #a #_ s1 s2 s3 =
  let aux (x:a)
    : Lemma (mem x (union (union s1 s2) s3) == mem x (union s1 (union s2 s3)))
    = union_mem_aux (union s1 s2) s3 x;
      union_mem_aux s1 s2 x;
      union_mem_aux s1 (union s2 s3) x;
      union_mem_aux s2 s3 x
  in
  Classical.forall_intro aux;
  eq_intro_aux (union (union s1 s2) s3) (union s1 (union s2 s3))
#pop-options

let rec add_size #a #f s x =
  match s with
  | [] -> ()
  | (y, _)::_ ->
    if x = y then ()
    else if f x y then ()
    else add_size (tl s) x

let rec length_size_aux (#a:eqtype) (#f:cmp a) (s:Seq.seq a)
  : Lemma
      (ensures Seq.length s == size (seq2mset #a #f s))
      (decreases (Seq.length s))
  = if Seq.length s = 0 then ()
    else
      let ms_tail = seq2mset #a #f (Seq.tail s) in
      add_size ms_tail (Seq.index s 0);
      length_size_aux #a #f (Seq.tail s)

let length_size = length_size_aux

let rec lemma_add_incr_mem_aux (#a:eqtype) (#f:cmp a) (s:mset a f) (x:a)
  : Lemma (ensures mem x (add_elem s x) = 1 + mem x s) =
  match s with
  | [] -> ()
  | (y,n)::_ -> 
    if x = y then ()
    else if f x y then mem_elt_lt_hd x s
    else lemma_add_incr_mem_aux (tl s) x

let lemma_add_incr_mem (#a:eqtype) (#f:cmp a) (s:mset a f) (x:a)
 : Lemma (ensures mem x (add_elem s x) = 1 + mem x s) = lemma_add_incr_mem_aux s x

let eq (#a:eqtype) (#f:cmp a) (s0 s1:mset a f) 
  : b:bool { b <==> (s0 == s1) }
  = s0 = s1
