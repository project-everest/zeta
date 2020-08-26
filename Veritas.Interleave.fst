module Veritas.Interleave
open FStar.Squash

let indexss (#a:Type) (ss: sseq a) (ij: sseq_index ss): Tot a = 
  let (i,j) = ij in
  index (index ss i) j

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

(* if s is sorted, any prefix of s is sorted *)
let lemma_sorted_prefix (#a:Type) (lte: a -> a -> bool) (s: seq a{sorted lte s}) (i:nat {i <= length s}):
  Lemma (sorted lte (prefix s i)) 
  = ()

let rec idx_of_greatest 
  (#a:eqtype) (lte: a-> a-> bool) 
  (ss: sseq a{flat_length ss > 0 /\ (forall (i:seq_index ss). sorted lte (index ss i))}): 
  Tot (j:seq_index ss{
    length (index ss j) > 0 /\
    (forall (k:seq_index ss). length (index ss k) > 0 ==> telem (index ss k) `lte` telem (index ss j))
  })
  (decreases (length ss)) =
  let n = length ss in
  let fn = flat_length ss in
  
  admit()

let rec sort_merge_aux (#a:eqtype) (lte: a-> a-> bool) 
               (ss: sseq a{forall (i:seq_index ss). sorted lte (index ss i)}):                
    Tot (interleave_ctor ss) = admit()

(* sort-merge interleaving *)
let sort_merge = sort_merge_aux

let lemma_sort_merge (#a:eqtype) (lte: a -> a -> bool)
  (ss: sseq a{forall (i: seq_index ss). sorted lte (index ss i)}):
  Lemma (requires (True))
        (ensures (sorted lte (interleaved_seq ss (sort_merge lte ss)))) = admit()

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
    if f x then
      admit()
    else (
      lemma_prefix1_append s' x;
      lemma_filter_extend1 f s;
      assert(fs' = fs);

      let aux (i:seq_index ss):
        Lemma (requires True)
              (ensures (index fss i = index fss' i))
              [SMTPat (index fss i)] = 
        assert(index fss i = filter f (index ss i));
        assert(index fss' i = filter f (index ss' i));
        
        if i = k then (          
          admit()
        )
        else 
          lemma_sseq_correct2 ss' x k i        
      in
      assert(equal fss fss');
      fprf'
    )

(* filter and interleaving commute (constructive version) *)
let lemma_filter_interleave_commute_prf (#a:eqtype) 
  (f:a -> bool) (s: seq a) (ss: sseq a) (prf: interleave s ss): 
  Tot (interleave (filter f s) (map (filter f) ss)) = 
  admit()


let lemma_filter_interleave_commute (#a:eqtype) (f:a -> bool) (s: seq a) (ss: sseq a{interleave s ss}):  
  Lemma (interleave (filter f s) (map (filter f) ss)) = admit()


(* map and interleaving commute (constructive version) *)
let lemma_map_interleave_commute_prf (#a #b: eqtype) (f: a -> b) (s: seq a) (ss: sseq a) (prf: interleave s ss):
  Tot (interleave (map f s) (map (map f) ss)) = admit()


(* map and interleaving commute *)
let lemma_map_interleave_commute (#a #b: eqtype) (f: a -> b) (s: seq a) (ss: sseq a{interleave s ss}):
  Lemma (interleave (map f s) (map (map f) ss)) = admit()


let interleaved_idx_seq (#a:eqtype) (ss: sseq a) (ic: interleave_ctor ss):
  Tot (seq (idx_elem #a (length ss))) = admit()

let lemma_interleaved_idx_seq (#a:eqtype) (ss:sseq a) (ic:interleave_ctor ss):
  Lemma (requires True)
        (ensures (interleave (project_seq (interleaved_idx_seq ss ic)) ss)) = admit()

let partition_idx_seq (#a:eqtype) (#n:nat) (s: seq (idx_elem #a n)):
  Tot (ss:sseq a{length ss = n}) = admit()
  
let lemma_interleave_idx_correct1 (#a:eqtype) (ss:sseq a) (ic:interleave_ctor ss):
  Lemma (requires True)
        (ensures (partition_idx_seq (interleaved_idx_seq ss ic) = ss)) = admit()

let partition_idx_seq_interleave_ctor (#a:eqtype) (#n:nat) (s:seq (idx_elem #a n)):
  Tot (interleave_ctor (partition_idx_seq s)) = admit()

let lemma_partition_idx_prefix_comm 
  (#a:eqtype) (#n:nat) (s:seq (idx_elem #a n)) (i:nat{i <= length s}) (id:nat{id < n}):
  Lemma (is_prefix (index (partition_idx_seq s) id)
                   (index (partition_idx_seq (prefix s i)) id)) = admit()

let lemma_partition_idx_extend1 (#a:eqtype) (#n:nat) (s: seq (idx_elem #a n){length s > 0}):
  Lemma (index (partition_idx_seq s) (snd (telem s)) = 
         append1 (index (partition_idx_seq (hprefix s)) (snd (telem s)))
                 (fst (telem s))) = admit()
