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

let sseq_extend (#a:eqtype) (ss: sseq a) (x:a) (i:seq_index ss): sseq a =
  let si = index ss i in
  let si' = append1 si x in
  upd ss i si'

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

type interleave (#a:eqtype): seq a -> ss:sseq a -> Type0 = 
  | IntEmpty: interleave (empty #a) (empty #(seq a))
  | IntAdd: s:seq a -> ss: sseq a -> prf:interleave s ss -> interleave s (append1 ss (empty #a))
  | IntExtend: s:seq a -> ss: sseq a -> prf:interleave s ss -> x:a -> i:seq_index ss ->
               interleave (append1 s x) (sseq_extend ss x i)

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
let empty_sseq_n a (n:nat) : sseq a = Seq.init #(seq a) n (fun _ -> empty #a)

let interleave_coerce_ss (#a:eqtype) (s:seq a) (ss0:sseq a) (ss1:sseq a{Seq.equal ss0 ss1})
                         (i:interleave s ss0)
  : interleave s ss1
  = i

#push-options "--print_implicits"
let rec interleave_empty_n (#a:eqtype) (n:nat) 
  : interleave #a empty (empty_sseq_n a n)
  = if n = 0 
    then (
      interleave_coerce_ss _ _ _ IntEmpty 
    )
    else (
      interleave_coerce_ss _ _ _ 
            (IntAdd _ _  (interleave_empty_n (n - 1)))
    )

let is_prefix_refl #a (s:seq a)
  : Lemma (is_prefix s s)
  = assert (SA.(prefix s (Seq.length s)) `Seq.equal` s)

let is_prefix_empty #a (s:seq a)
  : Lemma (is_prefix (empty #a) s)
  = assert (SA.(prefix s 0) `Seq.equal` (empty #a))

let sseq_prefix_all_refl (#a:eqtype) (ss:sseq a)
  : Lemma (sseq_prefix_all ss ss)
  = FStar.Classical.forall_intro (is_prefix_refl #a)

let sseq_prefix_all_empty (#a:eqtype) (ss:sseq a)
  : Lemma (sseq_prefix_all (empty_sseq_n a (Seq.length ss)) ss)
  = FStar.Classical.forall_intro (is_prefix_empty #a)

let sseq_prefix_all_extend (#a:eqtype) (ss0 ss1:sseq a) (x:a) (j:SA.seq_index ss1)
  : Lemma
    (requires sseq_prefix_all ss0 ss1)
    (ensures sseq_prefix_all ss0 (sseq_extend ss1 x j))
  = let ss1' = sseq_extend ss1 x j in
    let aux (tid:SA.seq_index ss1)
      : Lemma (is_prefix (Seq.index ss0 tid) (Seq.index ss1' tid))
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
    (requires sseq_prefix_all ss0 ss1 /\
              Seq.index ss0 j == Seq.index ss1 j)
    (ensures sseq_prefix_all (sseq_extend ss0 x j) (sseq_extend ss1 x j))
  = let ss0' = sseq_extend ss0 x j in
    let ss1' = sseq_extend ss1 x j in
    let aux (tid:SA.seq_index ss1)
      : Lemma (is_prefix (Seq.index ss0' tid) (Seq.index ss1' tid))
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
                            sseq_prefix_all (s_seq il') (s_seq il) /\
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
      assert (sseq_prefix_all (s_seq sub) ss);
      assert (s_seq il == append1 ss (empty #a));
      is_prefix_refl (empty #a);
      assert (sseq_prefix_all
                (append1 (s_seq sub) (empty #a))
                (append1 ss (empty #a)));
      IL _ _ (IntAdd _ _ (IL?.prf sub))
      
    | IL _ _ (IntExtend s ss il' x j) ->
      if i <= Seq.length s then (
        assert (Seq.equal (SA.prefix s i) (SA.prefix (append1 s x) i));
        let res = prefix_aux (IL s ss il') i in
        assert (sseq_prefix_all (s_seq res) ss);
        assert (s_seq il == sseq_extend ss x j);
        sseq_prefix_all_extend (s_seq res) ss x j;
        res
      )
      else (
        assert (i = Seq.length s + 1);
        let IL s' ss' prf = prefix_aux (IL s ss il') (i - 1) in
        assert (sseq_prefix_all ss' ss);
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
let lemma_prefix_prefix #a il i j = lemma_prefix_prefix_aux il i j

let filter (#a:eqtype) (f:a -> bool) (il:interleaving a)
  : interleaving a 
  = let IL is ss prf = il in
    IL (filter f is) (map (filter f) ss) (lemma_filter_interleave_commute_prf_aux f is ss prf)

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


(* broken ... not needed? *)
////////////////////////////////////////////////////////////////////////////////

// let rec project_seq_aux (#a:eqtype) (#n:nat) (is:seq (idx_elem #a n)): 
//   Tot (s:seq a{length s = length is})
//   (decreases (length is)) =
//   let n = length is in
//   if n = 0 then empty #a
//   else 
//     let is' = hprefix is in
//     let ps' = project_seq_aux is' in
//     let (e,id) = telem is in
//     append1 ps' e  

// let project_seq = project_seq_aux

// let rec lemma_project_seq_index_aux (#a:eqtype) (#n:nat) (is: seq (idx_elem #a n)) (i:seq_index is):
//   Lemma (requires True)
//         (ensures (fst (index is i) = index (project_seq is) i))
//         (decreases (length is)) =
//   let n = length is in
//   let ps = project_seq is in
//   if n = 0 then ()
//   else (
//     let is' = hprefix is in
//     let ps' = project_seq is' in
//     let (e,id) = telem is in
//     if i = n- 1 then ()
//     else
//       lemma_project_seq_index_aux is' i
//   )

// let lemma_project_seq_index = lemma_project_seq_index_aux

// let lemma_project_seq_extend (#a:eqtype) (#n:nat) (is: seq (idx_elem #a n){length is > 0}):
//   Lemma (project_seq is = append1 (project_seq (hprefix is)) (fst (telem is))) = 
//   ()

// let rec partition_idx_seq_aux (#a:eqtype) (#p:nat) (s: seq (idx_elem #a p)):
//   Tot (ss:sseq a{length ss = p}) 
//   (decreases (length s)) =
//   let n = length s in
//   if n = 0 then 
//     create p (empty #a)
//   else 
//     let s' = hprefix s in
//     let (e,id) = telem s in
//     let ss' = partition_idx_seq_aux s' in
//     sseq_extend ss' e id
  
// let partition_idx_seq = partition_idx_seq_aux

// let rec lemma_seq_empty_interleave_empty (#a:eqtype) (n:nat):
//   Tot (interleave (empty #a) (create n (empty #a)))
//   (decreases n) = 
//   let ln: sseq a = create n (empty #a) in
//   if n = 0 then (
//     lemma_empty ln;
//     IntEmpty
//   )
//   else (
//     let ln' = hprefix ln in
//     assert(equal ln' (create (n - 1) (empty #a)));
//     let prfn':interleave (empty #a) ln' = lemma_seq_empty_interleave_empty #a (n - 1) in
//     assert(equal ln (append1 ln' (empty #a)));
//     IntAdd (empty #a) ln' prfn' 
//   )

// let rec lemma_partition_idx_seq_interleaving_prf_aux (#a:eqtype) (#p:nat) (s: seq (idx_elem #a p)):
//   Tot (interleave (project_seq s) (partition_idx_seq s))
//   (decreases (length s)) =
//   let n = length s in 
//   let ps = project_seq s in
//   assert(length ps = n);  
//   if n = 0 then (
//     lemma_empty ps;
//     lemma_seq_empty_interleave_empty #a p
//   )
//   else (
//     let s' = hprefix s in
//     let ss' = partition_idx_seq s' in
//     let ps' = project_seq s' in
//     let (e,id) = telem s in
//     let prf': interleave ps' ss'  = lemma_partition_idx_seq_interleaving_prf_aux s' in
    
//     assert(ps = append1 ps' e);

//     let ss = partition_idx_seq s in
//     assert(ss == sseq_extend ss' e id);
  
//     IntExtend ps' ss' prf' e id
//   )

// let lemma_partition_idx_seq_interleaving_prf = lemma_partition_idx_seq_interleaving_prf_aux

// let lemma_partition_idx_seq_interleaving (#a:eqtype) (#n:nat) (s: seq (idx_elem #a n)):
//   Lemma (interleave (project_seq s) (partition_idx_seq s)) = 
//   return_squash (lemma_partition_idx_seq_interleaving_prf s)

// let rec lemma_partition_idx_prefix_comm_aux
//   (#a:eqtype) (#p:nat) (s:seq (idx_elem #a p)) (i:nat{i <= length s}) (id:nat{id < p}):
//   Lemma (requires True)
//         (ensures (is_prefix (index (partition_idx_seq s) id)
//                             (index (partition_idx_seq (prefix s i)) id)))
//         (decreases (length s)) =
//   let n = length s in
//   if n = i then ()
//   else (
//     assert(n > 0 && i < n);
//     let ps = partition_idx_seq s in
//     let s' = hprefix s in
//     let ps' = partition_idx_seq s' in
//     lemma_partition_idx_prefix_comm_aux s' i id;
//     assert(is_prefix (index ps' id)
//                      (index (partition_idx_seq (prefix s' i)) id));

//     let (e,id') = telem s in
//     if id' = id then (
//       assert(prefix s' i = prefix s i);
//       lemma_sseq_correct1 ps' e id';
//       assert(index ps id = append1 (index ps' id) e);
//       lemma_prefix1_append (index ps' id) e
//     )
//     else (
//       assert(ps == sseq_extend ps' e id');
//       lemma_sseq_correct2 ps' e id' id;
//       assert(index ps' id = index ps id);
//       ()
//     )
//   )

// let lemma_partition_idx_prefix_comm = lemma_partition_idx_prefix_comm_aux

// let lemma_partition_idx_extend1 (#a:eqtype) (#n:nat) (s: seq (idx_elem #a n){length s > 0}):
//   Lemma (index (partition_idx_seq s) (snd (telem s)) = 
//          append1 (index (partition_idx_seq (hprefix s)) (snd (telem s)))
//                  (fst (telem s))) = ()

// let to_s_idx_elem (#a:eqtype) (#p:nat) (e:idx_elem #a p): idx_elem #a (p+1) = 
//   let (x,i) = e in
//   (x,i)

// let to_s_idx_seq (#a:eqtype) (#p:nat) (s: seq (idx_elem #a p)): seq (idx_elem #a (p+1)) = 
//   map to_s_idx_elem s

// let rec interleaved_idx_seq_aux (#a:eqtype) (ss: sseq a) (ic: interleave_ctor ss):
//   Tot (seq (idx_elem #a (length ss))) 
//   (decreases (IntCtr?.prf ic)) = 
//   let p = length ss in
//   match ic with
//   | IntCtr s prf -> (
//     match prf with
    
//     | IntEmpty -> 
//       assert(ss == empty #(seq a));
//       empty #(idx_elem #a 0)
      
//     | IntAdd s' ss' prf' -> 
//       assert(s' == s);      
//       assert(ss = append1 ss' (empty #a));
      
//       let ic' = IntCtr s' prf' in
//       let is':seq (idx_elem #a (p-1)) = interleaved_idx_seq_aux ss' ic' in
//       let is:seq (idx_elem #a p) = to_s_idx_seq is' in      
//       is
      
//     | IntExtend s' ss' prf' x i ->
//       assert(length ss = length ss');
//       assert(s = append1 s' x);
//       let ic' = IntCtr s' prf' in
//       let is' = interleaved_idx_seq_aux ss' ic' in
//       append1 is' (x,i)
//   )

// let interleaved_idx_seq = interleaved_idx_seq_aux

// let rec lemma_s_idx_seq1 (#a:eqtype) (#p:nat) (is: seq (idx_elem #a p)) (idx:nat{idx < p}):
//   Lemma (requires True)
//         (ensures (index (partition_idx_seq is) idx = 
//                   index (partition_idx_seq (to_s_idx_seq is)) idx)) 
//         (decreases (length is))=             
//   let n = length is in
//   let iss = to_s_idx_seq is in
//   let ps = partition_idx_seq is in
//   let pss = partition_idx_seq iss in
//   if n = 0 then (
//     assert(partition_idx_seq is == create p (empty #a));
//     assert(partition_idx_seq iss == create (p+1) (empty #a));
//     ()
//   )
//   else (
//     let is' = hprefix is in
//     let ps' = partition_idx_seq is' in
//     let iss' = to_s_idx_seq is' in
//     let pss' = partition_idx_seq iss' in
//     let (e,i) = telem is in
//     lemma_map_extend to_s_idx_elem is;
//     lemma_prefix1_append iss' (to_s_idx_elem (telem is));
//     assert(pss == sseq_extend pss' e i);
//     assert(ps == sseq_extend ps' e i);

//     lemma_s_idx_seq1 is' idx;
//     assert(index ps' idx = index pss' idx);

//     assert(i < p);    

//     if i = idx then (
//       lemma_sseq_correct1 ps' e i;
//       lemma_sseq_correct1 pss' e i
//     )
//     else (
//       lemma_sseq_correct2 ps' e i idx;
//       lemma_sseq_correct2 pss' e i idx
//     )
//   )

// let rec lemma_s_idx_seq2 (#a:eqtype) (#p:nat) (is: seq (idx_elem #a p)):
//   Lemma (requires True)
//         (ensures (index (partition_idx_seq (to_s_idx_seq is)) p == empty #a)) 
//         (decreases (length is)) = 
//   let n = length is in        
//   let iss = to_s_idx_seq is in
//   let pss = partition_idx_seq iss in
//   if n = 0 then (
//     assert(partition_idx_seq iss == create (p+1) (empty #a));
//     ()
//   )
//   else (
//     let is' = hprefix is in
//     let iss' = to_s_idx_seq is' in
//     let pss' = partition_idx_seq iss' in
//     let (e,i) = telem is in
//     assert(i < p);        
//     lemma_map_extend to_s_idx_elem is;
//     lemma_prefix1_append iss' (to_s_idx_elem (telem is));
//     assert(pss == sseq_extend pss' e i);  

//     lemma_s_idx_seq2 is';
//     assert(index pss' p == empty #a);
//     lemma_sseq_correct2 pss' e i p
//   )

// let lemma_s_idx_seq (#a:eqtype) (#p:nat) (is: seq (idx_elem #a p)):
//   Lemma (partition_idx_seq (to_s_idx_seq is) = 
//          append1 (partition_idx_seq is) (empty #a)) = 
//   let iss = to_s_idx_seq is in
//   let pss = partition_idx_seq iss in
//   let ps = partition_idx_seq is in
//   let pss' = append1 ps (empty #a) in
//   assert(length pss = length pss');
//   let aux(i:nat{i <= p}):
//     Lemma (requires True)
//           (ensures (index pss i = index pss' i))
//           [SMTPat (index pss i)] = 
//     if i < p then 
//       lemma_s_idx_seq1 is i    
//     else
//       lemma_s_idx_seq2 is
//     in
//   assert(equal pss pss');
//   ()
                         
// let rec lemma_interleaved_idx_seq_correct_aux (#a:eqtype) (ss: sseq a) (ic: interleave_ctor ss):
//   Lemma (requires True)
//         (ensures (partition_idx_seq (interleaved_idx_seq ss ic) = ss)) 
//         (decreases (IntCtr?.prf ic)) = 
//   let is = interleaved_idx_seq ss ic in        
//   let ps = partition_idx_seq is in
//   match ic with
//   | IntCtr s prf -> (
//     match prf with
//     | IntEmpty -> 
//       lemma_empty ps
//     | IntAdd s' ss' prf' ->       
//       let ic' = IntCtr s' prf' in
//       let is' = interleaved_idx_seq ss' ic' in
//       let ps' = partition_idx_seq is' in
//       assert(is = to_s_idx_seq is');      
//       lemma_s_idx_seq is';
//       assert(ps = append1 ps' (empty #a));
//       lemma_interleaved_idx_seq_correct_aux ss' ic';
//       assert(ss' = ps');
//       assert(ss = append1 ss' (empty #a));
//       ()
//     | IntExtend s' ss' prf' x i ->
//       assert(length ss = length ss');
//       assert(s = append1 s' x);
//       let ic' = IntCtr s' prf' in
//       let is' = interleaved_idx_seq ss' ic' in
//       assert(is == append1 is' (x,i));
//       lemma_prefix1_append is' (x,i);

//       let ps' = partition_idx_seq is' in

//       lemma_interleaved_idx_seq_correct_aux ss' ic';
//       assert(ps' = ss');

//       assert(ps = sseq_extend ss' x i);
//       assert(ss = sseq_extend ss' x i);

//       ()
//   )

// let lemma_interleaved_idx_seq_correct = lemma_interleaved_idx_seq_correct_aux

// let rec lemma_partition_idx_seq (#a:eqtype) (#n:nat) (s: seq (idx_elem #a n)) (idx: nat{idx < n}):
//   Lemma (requires True)
//         (ensures (index (partition_idx_seq s) idx = 
//                   project_seq (filter (is_of_idx a n idx) s)))
//         (decreases (length s)) = 
//   let n = length s in 
//   let ss = partition_idx_seq s in
//   let ssi = index ss idx in
//   let si = filter (is_of_idx a n idx2) s in
  
//   if n = 0 then (
//     assert(length ssi = 0);
//     lemma_empty ssi;
//     assert(ssi == empty #a);
//     lemma_filter_empty (is_of_idx a n idx);
//     assert(si == empty #(idx_elem #a n));
//     admit()
//   )
//   else admit()


// let idx_seq_map (#a:eqtype) (#n:nat) (s:seq (idx_elem #a n)) (i: seq_index s):
//   Tot (j: sseq_index (partition_idx_seq s)
//   {
//       index (project_seq s) i = indexss (partition_idx_seq s) j /\
//       fst j = snd (index s i) 
//   }) = admit()

