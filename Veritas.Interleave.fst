module Veritas.Interleave
open FStar.Squash
module SA = Veritas.SeqAux
// let indexss (#a:Type) (ss: sseq a) (ij: sseq_index ss): Tot a = 
//   let (i,j) = ij in
//   index (index ss i) j

(* TODO: surely this should exists somewhere? *)
let nat_add (a b: nat): nat = a + b

(* sum of lengths of all sequences in a sequence of seqs *)
let flat_length (#a:Type) (ss: sseq a): 
  Tot nat = 
  reduce 0 nat_add (map length ss)

(* flat length of an empty sseq *)
let lemma_flat_length_empty (#a:Type):
  Lemma (flat_length (empty #(seq a)) = 0) = 
  let empty_ss = empty #(seq a) in
  let lens = map length empty_ss in
  
  assert(length lens = 0);
  lemma_empty lens;
  lemma_reduce_empty 0 nat_add

(* appending a singleton adds to the flat length *)
let lemma_flat_length_app1 (#a:Type) (ss: sseq a) (s: seq a)
  : Lemma (flat_length ss + length s = flat_length (append1 ss s)) = 
  let ss' = append1 ss s in
  lemma_prefix1_append ss s;
  lemma_map_extend length ss';
  lemma_reduce_append 0 nat_add (map length ss) (length s);
  ()

let lemma_append_extend (#a:Type) (s1: seq a) (s2: seq a{length s2 > 0}):
  Lemma (append s1 s2 == append1 (append s1 (hprefix s2)) (telem s2)) = 
  let s2' = hprefix s2 in
  let e2 = telem s2 in
  let aux (i: seq_index (append s1 s2)):
    Lemma (requires True)
          (ensures (index (append s1 s2) i == index (append1 (append s1 s2') e2) i))
          [SMTPat (index (append1 (append s1 s2') e2) i)] = ()
  in
  assert(equal (append s1 s2) (append1 (append s1 s2') e2));
  ()

let lemma_hprefix_append1 (#a:Type) (s: seq a{length s > 0}):
  Lemma (s == append1 (hprefix s) (telem s)) = 
  let s' = hprefix s in
  let e = telem s in
  let aux (i:seq_index s):
    Lemma (requires True)
          (ensures (index s i == index (append1 s' e) i))
          [SMTPat (index s i)] = ()
    in
  assert(equal s (append1 s' e));
  ()

(* appending adds to the flat length *)
let rec lemma_flat_length_app_aux (#a:Type) (ss1 ss2: sseq a)
  : Lemma (requires True)
          (ensures (flat_length ss1 + flat_length ss2 = flat_length (append ss1 ss2)))
          (decreases (length ss2)) =
  let n2 = length ss2 in
  if n2 = 0 then (
    lemma_empty ss2;
    lemma_flat_length_empty #a;
    append_empty_r ss1
  )
  else (
    let ss2' = hprefix ss2 in
    lemma_flat_length_app_aux ss1 ss2';
    lemma_append_extend ss1 ss2;
    lemma_flat_length_app1 (append ss1 ss2') (telem ss2);
    lemma_hprefix_append1 ss2;           
    lemma_flat_length_app1 ss2' (telem ss2)
  )

let lemma_flat_length_app = lemma_flat_length_app_aux

let lemma_sseq_correct1 (#a:eqtype) (ss: sseq a) (x:a) (i:seq_index ss):
  Lemma (index (sseq_extend ss x i) i = append1 (index ss i) x) = 
  ()

let lemma_sseq_correct2 (#a:eqtype) (ss: sseq a) (x:a) (i:seq_index ss) (j:seq_index ss{j <> i}):
  Lemma (index (sseq_extend ss x i) j = index ss j) = ()

let lemma_sseq_extend_len_base (#a:eqtype) (ss: sseq a{length ss > 0}) (x:a):
  Lemma (flat_length (sseq_extend ss x (length ss - 1)) = 1 + flat_length ss) = 
  let n = length ss in
  let i = n - 1 in
  let ss' = sseq_extend ss x i in  
  let ss'i = prefix ss' i in
  let ssi = prefix ss i in
  let iss' = suffix ss' (n - i) in
  let iss = suffix ss (n - i) in

  assert(equal ssi ss'i);

  let fl = flat_length ss in
  let fl' = flat_length ss' in
  let fli = flat_length ssi in

  let l = map length ss in
  let l' = map length ss' in
  
  let l'i = prefix l' i in
  let li = prefix l i in 
  assert(equal li l'i);

  let il' = suffix l' (n - i) in
  let il = suffix l (n - i) in


  lemma_reduce_prefix 0 nat_add l' i;
  lemma_reduce_prefix 0 nat_add l i;
  lemma_map_prefix length ss' i;
  lemma_map_prefix length ss i;
  assert(fl' = reduce fli nat_add il');  
  assert(fl = reduce fli nat_add il);

  lemma_reduce_singleton fli nat_add il';
  lemma_reduce_singleton fli nat_add il


let rec lemma_sseq_extend_len (#a:eqtype) (ss: sseq a) (x:a) (i:seq_index ss):
  Lemma (requires True)
        (ensures (flat_length (sseq_extend ss x i) = 1 + flat_length ss))
        (decreases (length ss)) = 
  let n = length ss in

  if i = n - 1 then (
    lemma_sseq_extend_len_base ss x
  )
  else (
    let ss' = hprefix ss in
    let ssx = sseq_extend ss x i in
    let ssx' = sseq_extend ss' x i in 

    lemma_sseq_extend_len ss' x i;
    assert(equal ssx (append1 ssx' (telem ss)));
    lemma_flat_length_app1 ssx' (telem ss);
    lemma_hprefix_append1 ss;
    lemma_flat_length_app1 ss' (telem ss)
  )


let rec lemma_interleave_len_prf (#a:eqtype) (s:seq a) (ss: sseq a) (prf:interleave s ss):
  Lemma (requires True)
        (ensures (length s = flat_length ss))
        (decreases prf) =
  match prf with
  | IntEmpty -> 
    assert(s == empty #a);
    assert(ss == empty #(seq a));
    lemma_flat_length_empty #a;
    ()
  | IntAdd s' ss' prf' -> 
    assert(s' == s);
    lemma_interleave_len_prf s' ss' prf';
    assert(length s = flat_length ss');
    assert(ss == append1 ss' (empty #a));
    lemma_flat_length_app1 ss' (empty #a);
    assert(flat_length ss' = flat_length ss);
    ()
  | IntExtend s' ss' prf' x i -> 
    assert(s == append1 s' x);
    assert(length s = length s' + 1);
    assert(ss == sseq_extend ss' x i);
    lemma_sseq_extend_len ss' x i;
    lemma_interleave_len_prf s' ss' prf'

let lemma_as_squash #a #b ($lem: (a -> Lemma b)) (x:a)
  : GTot (squash b)
  = lem x

let lemma_interleave_length (#a:eqtype) (s: seq a) (ss: sseq a{interleave s ss}):
  Lemma (length s = flat_length ss) = 
  bind_squash () (lemma_as_squash (lemma_interleave_len_prf s ss))

let rec interleave_map_aux (#a:eqtype) (s: seq a) (ss: sseq a)
     (prf:interleave #a s ss) (i: seq_index s): 
  Tot (j: (sseq_index ss){indexss ss j = index s i}) 
  (decreases prf) = 
  match prf with
  | IntEmpty -> 
    (* since i:nat < length s, a contradiction *)
    assert(length s = 0);
    (* return any value *)
    (0,0)
    
  | IntAdd s' ss' prf' -> 
    interleave_map_aux s' ss' prf' i
    
  | IntExtend s' ss' prf' x k ->
    assert(s == append1 s' x);
    
    if i = length s - 1 then (
      lemma_sseq_correct1 ss' x k;
      (k, length (index ss k) - 1)      
    )
    else (
      let (p,q) = interleave_map_aux s' ss' prf' i in
      if p = k then 
        (p,q)      
      else (
        lemma_sseq_correct2 ss' x k p;
        assert(index ss' p = index ss p);
        (p,q)
      )
    )

let interleave_map = interleave_map_aux

let rec interleave_map_inv_aux (#a:eqtype) (s: seq a) (ss: sseq a)
      (prf:interleave #a s ss) (i: sseq_index ss):
  Tot (j: seq_index s{index s j = indexss ss i})
  (decreases prf) = 
  let (p,q) = i in
  match prf with
  | IntEmpty -> 0
  | IntAdd s' ss' prf' -> 
    interleave_map_inv_aux s' ss' prf' i
    
  | IntExtend s' ss' prf' x k ->
    if p = k && q = length (index ss p) - 1 then (
      lemma_sseq_correct1 ss' x k;
      length s'
    )
    else (
      let r = interleave_map_inv_aux s' ss' prf' i in
      if p = k then (
        lemma_sseq_correct1 ss' x k;
        r
      )
      else (
        lemma_sseq_correct2 ss' x k p;
        r
      )
    )

let interleave_map_inv = interleave_map_inv_aux

let lemma_sseq_extend_filter_sat 
  (#a:eqtype) (f:a -> bool) (ss: sseq a) (x:a{f x}) (i:SA.seq_index ss):
  Lemma (map (filter f) (sseq_extend ss x i) = 
         sseq_extend (map (filter f) ss) x i) = 
  let ss' = sseq_extend ss x i in
  let fss' = map (filter f) ss' in
  let fss = map (filter f) ss in
  let fss2' = sseq_extend fss x i in
  let aux(j:SA.seq_index ss):
    Lemma (requires True)
          (ensures (Seq.index fss' j = Seq.index fss2' j))
          [SMTPat (Seq.index fss' j)] = 
    if j = i then (
      lemma_sseq_correct1 ss x i;
      lemma_prefix1_append (Seq.index ss i) x;
      lemma_filter_extend2 f (Seq.index ss' i)
    )
    else 
      lemma_sseq_correct2 ss x i j          
    in
  assert(equal fss' fss2');
  ()

(* filter and interleaving commute (constructive version) *)
let rec lemma_filter_interleave_commute_prf_aux (#a:eqtype) 
  (f:a -> bool) (s: seq a) (ss: sseq a) (prf: interleave s ss): 
  Tot (interleave (filter f s) (map (filter f) ss)) 
  (decreases prf) = 
  let fs = filter f s in
  let fss = map (filter f) ss in
  match prf with
  | IntEmpty -> 
    lemma_filter_empty f;
    lemma_empty fss;    
    IntEmpty 
    
  | IntAdd s' ss' prf' -> 
    let fss' = map (filter f) ss' in
    let fprf':(interleave fs fss')  = lemma_filter_interleave_commute_prf_aux f s' ss' prf' in
    lemma_prefix1_append ss' (empty #a);
    lemma_map_extend (filter f) ss;
    lemma_filter_empty f;
    IntAdd fs fss' fprf'
    
  | IntExtend s' ss' prf' x k ->
    assert(ss == sseq_extend ss' x k);
    let fss' = map (filter f) ss' in
    let fs' = filter f s' in
    let fprf':interleave fs' fss' = lemma_filter_interleave_commute_prf_aux f s' ss' prf' in
    if f x then (
      lemma_sseq_extend_filter_sat f ss' x k;
      lemma_prefix1_append s' x;
      lemma_filter_extend2 f s;
      IntExtend fs' fss' fprf' x k
    )
    else (
      lemma_prefix1_append s' x;
      lemma_filter_extend1 f s;
      assert(fs' = fs);
      let open FStar.Seq in
      let aux (i:SA.seq_index ss):
        Lemma (requires True)
              (ensures (Seq.index fss i = Seq.index fss' i))
              [SMTPat (Seq.index fss i)] = 
        assert(index fss i = filter f (index ss i));
        assert(index fss' i = filter f (index ss' i));
        
        if i = k then (
          lemma_sseq_correct1 ss' x k;
          lemma_prefix1_append (index ss' i) x;
          lemma_filter_extend1 f (index ss i)
        )
        else 
          lemma_sseq_correct2 ss' x k i        
      in
      assert(equal fss fss');
      fprf'
    )

(* filter and interleaving commute (constructive version) *)
let lemma_filter_interleave_commute_prf = lemma_filter_interleave_commute_prf_aux

let lemma_filter_interleave_commute_aux (#a:eqtype) (f:a -> bool) (s: seq a) (ss: sseq a)
  (prf:interleave s ss):  
  Lemma (interleave (filter f s) (map (filter f) ss)) = 
  return_squash (lemma_filter_interleave_commute_prf f s ss prf)
  
let lemma_filter_interleave_commute (#a:eqtype) (f:a -> bool) (s: seq a) (ss: sseq a{interleave s ss}):  
  Lemma (interleave (filter f s) (map (filter f) ss)) = 
  bind_squash () (lemma_as_squash (lemma_filter_interleave_commute_aux f s ss))

unfold 
let empty_sseq_n a (n:nat) : sseq a = Seq.create n empty


unfold
let sseq_equal (s0 s1:sseq 'a) =
  Seq.length s0 == Seq.length s1 /\
  (forall (i:SA.seq_index s0). Seq.index s0 i `Seq.equal` Seq.index s1 i) /\
  ((forall (i:SA.seq_index s0). Seq.index s0 i `Seq.equal` Seq.index s1 i) ==> Seq.equal s0 s1)
  

let interleave_coerce (#a:eqtype) 
                      (#s0:seq a) (#s1:seq a{Seq.equal s0 s1})
                      (#ss0:sseq a) (#ss1:sseq a{sseq_equal ss0 ss1})
                      (i:interleave s0 ss0)
  : interleave s1 ss1
  = i

let rec interleave_empty_n (#a:eqtype) (n:nat) 
  : interleave #a empty (empty_sseq_n a n)
  = if n = 0 
    then (
      interleave_coerce IntEmpty 
    )
    else (
      interleave_coerce 
            (IntAdd _ _  (interleave_empty_n (n - 1)))
    )

let is_prefix_refl (#a:eqtype) (s:seq a)
  : Lemma (s `prefix_of` s)
  = assert (SA.(prefix s (Seq.length s)) `Seq.equal` s)

let is_prefix_empty (#a:eqtype) (s:seq a)
  : Lemma (empty #a `prefix_of` s)
  = assert (SA.(prefix s 0) `Seq.equal` (empty #a))

let sseq_prefix_all_refl (#a:eqtype) (ss:sseq a)
  : Lemma (ss `sseq_all_prefix_of` ss)
  = FStar.Classical.forall_intro (is_prefix_refl #a)

let sseq_prefix_all_empty (#a:eqtype) (ss:sseq a)
  : Lemma ((empty_sseq_n a (Seq.length ss)) `sseq_all_prefix_of`  ss)
  = FStar.Classical.forall_intro (is_prefix_empty #a)

let sseq_prefix_all_extend (#a:eqtype) (ss0 ss1:sseq a) (x:a) (j:SA.seq_index ss1)
  : Lemma
    (requires ss0 `sseq_all_prefix_of` ss1)
    (ensures ss0 `sseq_all_prefix_of` (sseq_extend ss1 x j))
  = let ss1' = sseq_extend ss1 x j in
    let aux (tid:SA.seq_index ss1)
      : Lemma ((Seq.index ss0 tid) `prefix_of` (Seq.index ss1' tid))
              [SMTPat (Seq.index ss0 tid)]
      = if tid = j then (
           assert (Seq.equal (SA.prefix (Seq.index ss1' tid) (Seq.length (Seq.index ss1 tid))) 
                             (Seq.index ss1 tid))
        )
        else ()
    in
    ()

let sseq_prefix_all_extend_extend (#a:eqtype) (ss0 ss1:sseq a) (x:a) (j:SA.seq_index ss1)
  : Lemma
    (requires ss0 `sseq_all_prefix_of` ss1 /\
              Seq.index ss0 j == Seq.index ss1 j)
    (ensures (sseq_extend ss0 x j) `sseq_all_prefix_of` (sseq_extend ss1 x j))
  = let ss0' = sseq_extend ss0 x j in
    let ss1' = sseq_extend ss1 x j in
    let aux (tid:SA.seq_index ss1)
      : Lemma ((Seq.index ss0' tid) `prefix_of` (Seq.index ss1' tid))
              [SMTPat (Seq.index ss0 tid)]
      = if tid = j 
        then is_prefix_refl #a (Seq.index ss0' tid)
        else ()
    in
    ()

let rec interleave_empty #a #ss (i:interleave #a Seq.empty ss)
  : Lemma (ensures ss `Seq.equal` empty_sseq_n a (Seq.length ss))
          (decreases i)
  = match i with 
    | IntEmpty -> ()
    | IntAdd s ss prf -> interleave_empty prf

let rec prefix_aux (#a:eqtype) 
                   (il: interleaving a)
                   (i:nat{i <= length il})
  : Tot (il':interleaving a{i_seq il' = SA.prefix (i_seq il) i /\ 
                            S.length (s_seq il) = S.length (s_seq il') /\
                            (s_seq il') `sseq_all_prefix_of` (s_seq il) /\
                            (i == length il ==> s_seq il' == s_seq il)})
        (decreases (IL?.prf il))
  =         
  match i with
  | 0 -> 
    assert (Seq.equal (SA.prefix (i_seq il) i) empty);  
    let n = Seq.length (s_seq il) in
    sseq_prefix_all_empty (s_seq il);
    let _ = 
      if length il = 0
      then (assert (i_seq il `Seq.equal` Seq.empty #a);
            interleave_empty #a #(s_seq il) (IL?.prf il);
            assert (s_seq il == empty_sseq_n a (Seq.length (s_seq il))))
      else ()
    in
    IL _ _ (interleave_empty_n n)
  | _ ->
    match il with
    | IL _ _ (IntAdd s ss il') ->
      let sub = prefix_aux (IL s ss il') i in
      assert ((s_seq sub) `sseq_all_prefix_of` ss);
      assert (s_seq il == append1 ss (empty #a));
      is_prefix_refl (empty #a);
      assert (sseq_all_prefix_of
                (append1 (s_seq sub) (empty #a))
                (append1 ss (empty #a)));
      IL _ _ (IntAdd _ _ (IL?.prf sub))
      
    | IL _ _ (IntExtend s ss il' x j) ->
      if i <= Seq.length s then (
        assert (Seq.equal (SA.prefix s i) (SA.prefix (append1 s x) i));
        let res = prefix_aux (IL s ss il') i in
        assert ((s_seq res) `sseq_all_prefix_of` ss);
        assert (s_seq il == sseq_extend ss x j);
        sseq_prefix_all_extend (s_seq res) ss x j;
        res
      )
      else (
        assert (i = Seq.length s + 1);
        let IL s' ss' prf = prefix_aux (IL s ss il') (i - 1) in
        assert (ss' `sseq_all_prefix_of` ss);
        sseq_prefix_all_extend_extend ss' ss x j;        
        IL _ _ (IntExtend _ _ prf x j)
      )

let prefix #a il i = prefix_aux #a il i

let per_thread_prefix (#a:eqtype) (il: interleaving a) (i:nat{i <= length il})
  = ()
  
let rec i2s_map_aux (#a:eqtype) (il:interleaving a) (i:seq_index il) 
  : Tot (si:sseq_index (s_seq il) {index il i = indexss (s_seq il) si})
        (decreases (IL?.prf il))
  = let IL is ss prf = il in
    match prf with
    | IntAdd _ ss' prf' -> 
      i2s_map_aux (IL is ss' prf') i 
    | IntExtend is' ss' prf' x j ->
      if i < Seq.length is'
      then i2s_map_aux (IL is' ss' prf') i
      else (j, Seq.length (Seq.index ss' j))

let rec s2i_map_aux (#a:eqtype) (il:interleaving a) (si: sseq_index (s_seq il))
  : Tot (i:seq_index il{index il i = indexss (s_seq il) si /\
                        i2s_map_aux il i == si})
        (decreases (IL?.prf il))
  = let IL is ss prf = il in
    match prf with 
    | IntEmpty -> false_elim()
    | IntAdd _ ss' prf' ->
      s2i_map_aux (IL is ss' prf') si
    | IntExtend is' ss' prf' x j ->
      if fst si <> j ||
         snd si < Seq.length (Seq.index ss' j)
      then s2i_map_aux (IL is' ss' prf') si
      else Seq.length is'

let i2s_map #a il i = i2s_map_aux il i
let s2i_map #a il si = s2i_map_aux il si

let lemma_i2s_s2i (#a:eqtype) (il:interleaving a) (i:seq_index il) 
  = let rec aux (il:interleaving a) (i:seq_index il)
      : Lemma (ensures s2i_map il (i2s_map il i) == i)
              (decreases (IL?.prf il))
      = let IL is ss prf = il in
        match prf with
        | IntAdd _ ss' prf' ->
          aux (IL is ss' prf') i
        | IntExtend is' ss' prf' x j ->
          if i < Seq.length is' 
          then aux (IL is' ss' prf') i
          else ()
    in
    aux il i

let lemma_prefix_index (#a:eqtype) (il:interleaving a) (i:nat{i <= length il}) (j:nat{j < i}) 
  = ()

#push-options "--z3rlimit_factor 2"
let lemma_prefix_prefix_aux (#a:eqtype) (il:interleaving a) (i:nat{i <= length il}) (j:nat{j <= i})
  : Lemma (ensures (prefix (prefix il i) j == prefix il j))
  = let rec aux (il:interleaving a) (i:nat{i <= length il}) (j:nat{j <= i})
      : Lemma (ensures (prefix (prefix il i) j == prefix il j))
              (decreases (IL?.prf il))
      = let IL is ss prf = il in 
        match prf with
        | IntEmpty -> ()
        | IntAdd _ ss' prf' ->
          aux (IL is ss' prf') i j
        | IntExtend is' ss' prf' x k ->
          if j <= Seq.length is' then (
            if i <= Seq.length is' then (
              aux (IL is' ss' prf') i j
            )
            else (
              assert (i == Seq.length is' + 1);
              aux (IL is' ss' prf') (i - 1) j
            )
          )
          else (
            assert (i == j);
            aux (IL is' ss' prf') (i - 1) (j - 1)
          )
    in
    aux il i j
#pop-options
let lemma_prefix_prefix #a il i j = lemma_prefix_prefix_aux il i j

let filter_interleaving #a f #s #ss i =
  lemma_filter_interleave_commute_prf_aux f s ss i

let rec lemma_i2s_map_prefix_aux (#a:eqtype) (il: interleaving a) (i: nat{i <= length il}) (j:nat{j < i}) 
  : Lemma (ensures i2s_map il j == i2s_map (prefix il i) j)
          (decreases (IL?.prf il))
  = let IL is ss prf = il in
    match prf with
    | IntEmpty -> false_elim()
    | IntAdd _ ss' prf' ->
      lemma_i2s_map_prefix_aux (IL is ss' prf') i j
    | IntExtend is' ss' prf' x k -> 
      if i <= Seq.length is'
      then lemma_i2s_map_prefix_aux (IL is' ss' prf') i j
      else (
        assert (i == Seq.length is);
        if j = (i - 1) then (
          ()
        )  
        else (
          lemma_i2s_map_prefix_aux (IL is' ss' prf') (i - 1) j
        )
      )

let lemma_i2s_map_prefix #a il i j = lemma_i2s_map_prefix_aux il i j

let lemma_prefix_interleaving (#a:eqtype) 
  (il: interleaving a) 
  (i:nat{ i <= length il}) 
  (j:nat{j < S.length (s_seq il)}) = 
  per_thread_prefix il i

let lemma_prefix_snoc (#a:eqtype) (il:interleaving a) (i:seq_index il)
  = let rec aux (il:interleaving a) (i:seq_index il)
      : Lemma 
        (ensures
            (let tid, j = i2s_map il i in
             let il_i = prefix il i in
             let il_i' = prefix il (i + 1) in
             Seq.index (s_seq il_i') tid `Seq.equal` Seq.snoc (Seq.index (s_seq il_i) tid) (index il i)))
        (decreases (IL?.prf il))
      = let IL is ss prf = il in
        match prf with
        | IntAdd _ ss' prf' -> 
          aux (IL is ss' prf') i
        | IntExtend is' ss' prf' x j ->
          if i < Seq.length is'
          then aux (IL is' ss' prf') i
    in
    aux il i

let rec map_interleave (#a #b:eqtype) (f:a -> b) (s:seq a) (ss:sseq a) (i:interleave s ss)
   : Tot (interleave (map f s) (map (map f) ss))
         (decreases i)
   = match i with
     | IntEmpty -> 
       interleave_coerce IntEmpty
     | IntAdd _ ss' prf' -> 
       interleave_coerce (IntAdd _ _ (map_interleave f _ _ prf'))
     | IntExtend s' ss' prf' x j -> 
       interleave_coerce (IntExtend _ _ (map_interleave f _ _ prf') (f x) j)

let map_interleave_i2s (#a #b:eqtype) (f:a -> b) (prf:interleaving a) (i:seq_index prf)
  : Lemma (ensures (i2s_map prf i == i2s_map (IL _ _ (map_interleave f _ _ (IL?.prf prf))) i))
  = let rec aux (prf:interleaving a) (i:seq_index prf)
      : Lemma (ensures (i2s_map prf i == i2s_map (IL _ _ (map_interleave f _ _ (IL?.prf prf))) i))
              (decreases (IL?.prf prf))
      = let IL is ss prf = prf in
        match prf with
        | IntAdd _ ss' prf' ->
          aux (IL _ _ prf') i
        | IntExtend is' ss' prf' x j ->
          if i < Seq.length is'
          then aux (IL _ _ prf') i
    in
    aux prf i
