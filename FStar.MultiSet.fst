module FStar.MultiSet

open FStar.List.Tot

type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
  (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2) /\  (* anti-symmetry *)
  (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3) /\  (* transitivity  *)
  (forall a1 a2. f a1 a2 \/ f a2 a1)                   (* totality      *)

type cmp (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}

let rec sorted (#a:eqtype) (f:cmp a) (l:list (a & pos)) : Tot bool =
  match l with
  | [] -> true
  | [_] -> true
  | (x, _)::(y, card_y)::tl -> f x y && x <> y && sorted f ((y, card_y)::tl)

type mset (a:eqtype) (f:cmp a) = l:list (a & pos){sorted f l}

let rec mem (#a:eqtype) (#f:cmp a) (x:a) (s:mset a f) : nat =
  match s with
  | [] -> 0
  | (y, card_y)::tl -> if x = y then card_y else mem #a #f x tl

let rec mem_elt_lt_hd (#a:eqtype) (#f:cmp a) (x:a) (s:mset a f{Cons? s})
  : Lemma
      (requires f x (fst (Cons?.hd s)) /\ x <> fst (Cons?.hd s))
      (ensures mem x s == 0)
  = match s with
    | [_] -> ()
    | _::tl -> mem_elt_lt_hd #a #f x tl

let rec mem_hd_in_tl (#a:eqtype) (#f:cmp a) (s:mset a f{Cons? s})
  : Lemma
      (requires True)
      (ensures mem #a #f (fst (Cons?.hd s)) (Cons?.tl s) == 0)
      (decreases (length s))
  = match s with
    | [_] -> ()
    | (x, card_x)::(y, _)::tl -> mem_hd_in_tl #a #f ((x, card_x)::tl)

let contains (#a:eqtype) (#f:cmp a) (x:a) (s:mset a f) = mem x s > 0

let equal (#a:eqtype) (#f:cmp a) (s1 s2:mset a f) = s1 = s2

let forall_x_mem_in_tl (#a:eqtype) (#f:cmp a) (s1 s2:mset a f)
  : Lemma
      (requires
        (forall (x:a). mem x s1 == mem x s2) /\
        Cons? s1 /\ Cons? s2)
      (ensures
        forall (x:a). mem #a #f x (Cons?.tl s1) == mem #a #f x (Cons?.tl s2))
  = let aux (x:a)
      : Lemma (mem #a #f x (Cons?.tl s1) == mem #a #f x (Cons?.tl s2))
      = match s1, s2 with
        | (x1, _)::_, (x2, _)::_ ->
          if x1 = x2 then
            if x1 = x then begin
              mem_hd_in_tl s1;
              mem_hd_in_tl s2
            end
            else ()
          else if f x1 x2 then mem_elt_lt_hd x1 s2
          else mem_elt_lt_hd x2 s1
    in
    Classical.forall_intro aux

let rec lemma_eq_intro (#a:eqtype) (#f:cmp a) (s1 s2:mset a f)
  : Lemma
      (requires forall (x:a). mem x s1 == mem x s2)
      (ensures equal s1 s2)
  = match s1, s2 with
    | [], [] -> ()
    | (x, _)::_, [] -> assert (mem x s1 > 0); assert (mem x s2 == 0)
    | [], (x, _)::_ -> assert (mem x s1 == 0); assert (mem x s2 > 0)
    | (x, card_x)::tl1, (y, card_y)::tl2 ->
      if x = y then begin
        forall_x_mem_in_tl s1 s2;
        lemma_eq_intro #a #f tl1 tl2
      end
      else if f x y then mem_elt_lt_hd x s2
      else mem_elt_lt_hd y s1

let lemma_eq_refl (#a:eqtype) (#f:cmp a) (s1 s2:mset a f)
  : Lemma
      (requires s1 == s2)
      (ensures equal s1 s2)
  = ()

let lemma_eq_elim (#a:eqtype) (#f:cmp a) (s1 s2:mset a f)
  : Lemma
      (requires equal s1 s2)
      (ensures s1 == s2)
  = ()

let lemma_not_equal (#a:eqtype) (#f:cmp a) (s1 s2:mset a f) (x:a)
  : Lemma
      (requires mem x s1 <> mem x s2)
      (ensures (~ (s1 == s2)))
  = ()

let rec size (#a:eqtype) (#f:cmp a) (s:mset a f) : nat =
  match s with
  | [] -> 0
  | (_, card)::tl -> card + size #a #f tl

let empty (#a:eqtype) (#f:cmp a) : mset a f = []

let create (#a:eqtype) (#f:cmp a) (x:a) (m:pos) : mset a f = [x, m]

(* private *)
let rec add (#a:eqtype) (#f:cmp a) (x:a) (s:mset a f)
  : s':mset a f{
      Cons? s' /\
      (fst (Cons?.hd s') == x \/ (Cons? s /\ fst (Cons?.hd s') == fst (Cons?.hd s)))}
  = match s with
    | [] -> [x, 1]
    | (y, card_y)::tl ->
      if x = y then (y, card_y + 1)::tl
      else if f x y then (x, 1)::s
      else (y, card_y)::(add #a #f x tl)

let rec add_mem (#a:eqtype) (#f:cmp a) (x:a) (s:mset a f)
  : Lemma (mem #a #f x (add x s) == mem x s + 1)
  = match s with
    | [] -> ()
    | (y, _)::tl ->
      if x = y then ()
      else if f x y then mem_elt_lt_hd x s
      else add_mem #a #f x tl

let rec add_mem_neq (#a:eqtype) (#f:cmp a) (x:a) (s:mset a f) (y:a{x =!= y})
  : Lemma (mem #a #f y (add x s) == mem #a #f y s)
  = match s with
    | [] -> ()
    | (z, _)::tl ->
      if x = z then ()
      else if f x z then ()
      else add_mem_neq #a #f x tl y

let rec seq2mset (#a:eqtype) (#f:cmp a) (s:Seq.seq a) : Tot (mset a f) (decreases (Seq.length s)) =
  if Seq.length s = 0 then empty
  else
    let ms = seq2mset (Seq.slice s 1 (Seq.length s)) in
    add (Seq.index s 0) ms

let rec lemma_count_mem_aux (#a:eqtype) (#f:cmp a) (s:Seq.seq a) (x:a)
  : Lemma
      (requires True)
      (ensures Seq.count x s == mem x (seq2mset #a #f s))
      (decreases (Seq.length s))
  = if Seq.length s = 0 then ()
    else begin
      lemma_count_mem_aux #a #f (Seq.slice s 1 (Seq.length s)) x;
      if Seq.index s 0 = x
      then add_mem x (seq2mset #a #f (Seq.slice s 1 (Seq.length s)))
      else add_mem_neq (Seq.index s 0) (seq2mset #a #f (Seq.slice s 1 (Seq.length s))) x
    end


type seq_index (#a:eqtype) (s:Seq.seq a) = n:nat{n < Seq.length s}

let smap (#a:eqtype) (s1 s2:Seq.seq a) =
  f:(seq_index s1 -> seq_index s2){forall (i:seq_index s1). Seq.index s1 i == Seq.index s2 (f i)}

let into_smap (#a:eqtype) (s1 s2:Seq.seq a) =
  f:smap s1 s2{forall (i j:seq_index s1). f i == f j ==> i == j}

let seq_remove (#a:eqtype) (s:Seq.seq a) (i:seq_index s)
  : Seq.seq a
  = Seq.append (Seq.slice s 0 i) (Seq.slice s (i + 1) (Seq.length s))

let seq_remove_count1 (#a:eqtype) (s:Seq.seq a) (i:seq_index s)
  : Lemma (Seq.count (Seq.index s i) s == Seq.count (Seq.index s i) (seq_remove s i) + 1)
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

let seq_remove_count2 (#a:eqtype) (s:Seq.seq a) (i:seq_index s) (y:a{y =!= Seq.index s i})
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

let ismap_next (#a:eqtype) (s1:Seq.seq a{Seq.length s1 > 0}) (s2:Seq.seq a) (f:into_smap s1 s2)
  : into_smap (Seq.slice s1 1 (Seq.length s1))
              (seq_remove s2 (f 0))
  = let s1' = Seq.slice s1 1 (Seq.length s1) in
    let s2' = seq_remove s2 (f 0) in
    let f : seq_index s1' -> seq_index s2' = fun i ->
      let n = f (i + 1) in
      if n < f 0 then n
      else n - 1 in

    f

let rec seq_count_into_smap_x (#a:eqtype) (s1 s2:Seq.seq a) (f:into_smap s1 s2) (x:a)
  : Lemma
      (requires True)
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

let seq_count_into_smap (#a:eqtype) (s1 s2:Seq.seq a) (f:into_smap s1 s2)
  : Lemma (forall (x:a). Seq.count x s1 <= Seq.count x s2)
  = let aux (x:a) : Lemma (Seq.count x s1 <= Seq.count x s2) [SMTPat ()]
      = seq_count_into_smap_x s1 s2 f x
    in ()

let lemma_count_mem (#a:eqtype) (#f:cmp a) (s:Seq.seq a) (x:a)
  : Lemma (Seq.count x s == mem x (seq2mset #a #f s))
  = lemma_count_mem_aux #a #f s x

let lemma_mset_bijection (#a:eqtype) (#f:cmp a) (s1 s2:Seq.seq a) (f12:into_smap s1 s2) (f21:into_smap s2 s1)
  : Lemma (seq2mset #a #f s1 == seq2mset #a #f s2)
  = seq_count_into_smap s1 s2 f12;
    seq_count_into_smap s2 s1 f21;
    Classical.forall_intro (lemma_count_mem #a #f s1);
    Classical.forall_intro (lemma_count_mem #a #f s2);
    lemma_eq_intro #a #f (seq2mset #a #f s1) (seq2mset #a #f s2);
    lemma_eq_elim #a #f (seq2mset #a #f s1) (seq2mset #a #f s2)

let rec seq_count_i (#a:eqtype) (s:Seq.seq a) (i:seq_index s)
  : Lemma
      (requires True)
      (ensures Seq.count (Seq.index s i) s > 0)
      (decreases (Seq.length s))
  = if i = 0 then ()
    else seq_count_i (Seq.slice s 1 (Seq.length s)) (i - 1)

let lemma_seq_elem (#a:eqtype) (#f:cmp a) (s:Seq.seq a) (i:seq_index s)
  : Lemma (contains (Seq.index s i) (seq2mset #a #f s))
  = seq_count_i s i;
    lemma_count_mem #a #f s (Seq.index s i)

let rec union (#a:eqtype) (#f:cmp a) (s1 s2:mset a f) :
  s:mset a f{
    ((Cons? s1 /\ Cons? s2) ==>
     (Cons? s /\ (let x1 = fst (Cons?.hd s1) in
                 let x2 = fst (Cons?.hd s2) in
                 if f x1 x2 then fst (Cons?.hd s) == x1
                 else fst (Cons?.hd s) == x2))) /\
    (Nil? s1 ==> s == s2) /\
    (Nil? s2 ==> s == s1)} =
  match s1, s2 with
  | [], _ -> s2
  | _, [] -> s1
  | (x1, card1)::tl1, (x2, card2)::tl2 ->
    if x1 = x2
    then (x1, card1 + card2)::(union #a #f tl1 tl2)
    else if f x1 x2
    then (x1, card1)::(union #a #f tl1 s2)
    else (x2, card2)::(union #a #f s1 tl2)

let rec lemma_union_count (#a:eqtype) (#f:cmp a) (s1 s2:mset a f) (x:a)
  : Lemma (mem x (union s1 s2) == mem x s1 + mem x s2)
  = match s1, s2 with
    | [], _ -> ()
    | _, [] -> ()
    | (x1, card1)::tl1, (x2, card2)::tl2 ->
      if x1 = x2
      then lemma_union_count #a #f tl1 tl2 x
      else if f x1 x2
      then begin
        lemma_union_count #a #f tl1 s2 x;
        if x = x1
        then mem_elt_lt_hd x s2
        else if f x x1
        then (mem_elt_lt_hd x s1; mem_elt_lt_hd x s2)
      end
      else begin
        lemma_union_count #a #f s1 tl2 x;
        if x = x2
        then mem_elt_lt_hd x s1
        else if f x x2
        then (mem_elt_lt_hd x s2; mem_elt_lt_hd x s1)
      end

let lemma_union_comm (#a:eqtype) (#f:cmp a) (s1 s2:mset a f)
  : Lemma (union #a #f s1 s2 == union #a #f s2 s1)
  = Classical.forall_intro (lemma_union_count s1 s2);
    Classical.forall_intro (lemma_union_count s2 s1);
    lemma_eq_intro (union s1 s2) (union s2 s1);
    lemma_eq_elim (union s1 s2) (union s2 s1)

let lemma_union_assoc (#a:eqtype) (#f:cmp a) (s1 s2 s3:mset a f)
  : Lemma (union (union s1 s2) s3 == union s1 (union s2 s3))
  = Classical.forall_intro (lemma_union_count s1 s2);
    Classical.forall_intro (lemma_union_count s2 s3);
    Classical.forall_intro (lemma_union_count (union s1 s2) s3);
    Classical.forall_intro (lemma_union_count s1 (union s2 s3));
    lemma_eq_intro (union (union s1 s2) s3) (union s1 (union s2 s3));
    lemma_eq_elim (union (union s1 s2) s3) (union s1 (union s2 s3))

let lemma_union_append (#a:eqtype) (#f:cmp a) (s1 s2:Seq.seq a)
  : Lemma (seq2mset #a #f (Seq.append s1 s2) == union (seq2mset #a #f s1) (seq2mset #a #f s2))
  = Seq.lemma_append_count s1 s2;
    Classical.forall_intro (lemma_count_mem #a #f s1);
    Classical.forall_intro (lemma_count_mem #a #f s2);    
    Classical.forall_intro (lemma_count_mem #a #f (Seq.append s1 s2));
    Classical.forall_intro (lemma_union_count (seq2mset #a #f s1) (seq2mset #a #f s2));
    lemma_eq_intro (seq2mset #a #f (Seq.append s1 s2)) (union (seq2mset #a #f s1) (seq2mset #a #f s2));
    lemma_eq_elim (seq2mset #a #f (Seq.append s1 s2)) (union (seq2mset #a #f s1) (seq2mset #a #f s2))

let is_set (#a:eqtype) (#f:cmp a) (s:mset a f) = forall (x:a). mem x s <= 1

let rec diff_elem (#a:eqtype) (#f:cmp a) (s1 s2:mset a f)
  : Pure a
      (requires size s1 > size s2)
      (ensures fun x -> mem x s1 > mem x s2)
  = match s1, s2 with
    | (x, _)::_, [] -> x
    | (x1, card1)::tl1, (x2, card2)::tl2 ->
      if x1 = x2
      then if card1 > card2 then x1
           else begin
             mem_hd_in_tl s1;
             diff_elem #a #f tl1 tl2
           end
      else if f x1 x2 then begin
        mem_elt_lt_hd x1 s2;
        x1
      end
      else begin
        mem_elt_lt_hd x2 s1;
        diff_elem s1 tl2
      end

let add_elem (#a:eqtype) (#f:cmp a) (s:mset a f) (x:a) : mset a f = add x s

let rec lemma_add_size (#a:eqtype) (#f:cmp a) (s:mset a f) (x:a)
  : Lemma (size (add_elem s x) == size s + 1)
  = match s with
    | [] -> ()
    | (y, card_y)::tl ->
      if x = y then ()
      else if f x y then ()
      else lemma_add_size #a #f tl x

let append1 (#a:eqtype) (s:Seq.seq a) (x:a) = Seq.append s (Seq.create 1 x)

let lemma_add_elem (#a:eqtype) (#f:cmp a) (s:Seq.seq a) (x:a)
  : Lemma (seq2mset #a #f (append1 s x) == add_elem (seq2mset #a #f s) x)
  = Seq.lemma_append_count s (Seq.create 1 x);

    add_mem x (seq2mset #a #f s);
    Classical.forall_intro (add_mem_neq #a #f x (seq2mset #a #f s));

    Classical.forall_intro (lemma_count_mem #a #f (append1 s x));
    Classical.forall_intro (lemma_count_mem #a #f s);

    lemma_eq_intro (seq2mset #a #f (append1 s x)) (add_elem (seq2mset #a #f s) x);
    lemma_eq_elim (seq2mset #a #f (append1 s x)) (add_elem (seq2mset #a #f s) x)

let rec index_of_mselem (#a:eqtype) (#f:cmp a) (s:Seq.seq a) (x:a{contains x (seq2mset #a #f s)})
  : Tot (i:seq_index s{Seq.index s i == x}) (decreases (Seq.length s))
  = if Seq.index s 0 = x then 0
    else begin
      add_mem_neq #a #f (Seq.index s 0) (seq2mset #a #f (Seq.slice s 1 (Seq.length s))) x;
      1 + index_of_mselem #a #f (Seq.slice s 1 (Seq.length s)) x
    end

let is_prefix (#a:eqtype) (s:Seq.seq a) (ps:Seq.seq a) =
  Seq.length ps <= Seq.length s /\
  ps == Seq.slice s 0 (Seq.length ps)

let rec seq_count_is_prefix (#a:eqtype) (s1 s2:Seq.seq a) (x:a)
  : Lemma
      (requires is_prefix s1 s2)
      (ensures Seq.count x s2 <= Seq.count x s1)
      (decreases (Seq.length s1))
  = if Seq.length s2 = 0 then ()
    else seq_count_is_prefix (Seq.tail s1) (Seq.tail s2) x

let lemma_prefix_mem (#a:eqtype) (#f:cmp a) (s:Seq.seq a) (s':Seq.seq a{is_prefix s s'}) (x:a)
  : Lemma (mem x (seq2mset #a #f s') <= mem x (seq2mset #a #f s))
  = seq_count_is_prefix s s' x;
    lemma_count_mem #a #f s x;
    lemma_count_mem #a #f s' x

let rec lemma_seq_elem2_aux (#a:eqtype) (s:Seq.seq a) (i1 i2:seq_index s)
  : Lemma
      (requires i1 =!= i2 /\ Seq.index s i1 == Seq.index s i2)
      (ensures Seq.count (Seq.index s i1) s >= 2)
      (decreases (Seq.length s))
  = if i1 = 0 then seq_count_i (Seq.slice s 1 (Seq.length s)) (i2 - 1)
    else if i2 = 0 then seq_count_i (Seq.slice s 1 (Seq.length s)) (i1 - 1)
    else lemma_seq_elem2_aux (Seq.slice s 1 (Seq.length s)) (i1 - 1) (i2 - 1)

let lemma_seq_elem2 (#a:eqtype) (#f:cmp a) (s:Seq.seq a) (i1 i2:seq_index s)
  : Lemma
      (requires i1 =!= i2 /\ Seq.index s i1 == Seq.index s i2)
      (ensures mem (Seq.index s i1) (seq2mset #a #f s) >= 2)
  = lemma_seq_elem2_aux #a s i1 i2;
    lemma_count_mem #a #f s (Seq.index s i1)
