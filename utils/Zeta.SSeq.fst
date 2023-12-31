module Zeta.SSeq

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
  Lemma (ensures (flat_length (sseq_extend ss x i) = 1 + flat_length ss))
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

let rec lemma_flat_length_emptyn (a:_) (n:nat)
  : Lemma (ensures (flat_length (empty a n) = 0))
          (decreases n)
  = let ss = empty a n in
    if n = 0 then (
      lemma_empty ss;
      lemma_flat_length_empty #a
    )
    else (
      let ss' = empty a (n-1) in
      lemma_flat_length_emptyn a (n-1);
      let ssc = append1 ss' (FStar.Seq.empty #a) in
      let aux(i: seq_index ss)
        : Lemma (ensures (index ss i == index ssc i))
                [SMTPat (index ss i == index ssc i)]
        =  ()
      in
      assert(equal ss ssc);
      lemma_flat_length_app1 ss' (FStar.Seq.empty #a)
    )

let rec lemma_flat_length_zero (#a:_) (ss: sseq a {flat_length ss = 0})
  : Lemma (ensures (ss == empty a (length ss)))
          (decreases (length ss))
  = let n = length ss in
    let en = empty a (length ss) in
    if n = 0 then (
      lemma_empty ss;
      let aux(i: seq_index ss)
        : Lemma (ensures (index ss i == index en i))
                [SMTPat (index ss i == index en i)]
        = ()
      in
      assert(equal ss en)
    )
    else (
      let ss' = prefix ss (n - 1) in
      let s = index ss (n - 1) in
      lemma_hprefix_append_telem ss;
      //assert(ss == append1 ss' s);
      lemma_flat_length_app1 ss' s;
      //assert(length s = 0);
      lemma_empty s;
      //assert(flat_length ss' = 0);
      lemma_flat_length_zero ss';
      //assert(ss' == empty a (n-1));
      //assert(length ss = length en);
      let aux (i: seq_index ss)
        : Lemma (ensures (index ss i == index en i))
        = ()
      in
      FStar.Classical.forall_intro aux;
      assert(equal ss en)
    )

let sseq_prefix_append (#a:eqtype) (ss: sseq a) (i: seq_index ss{length (index ss i) > 0})
  : Lemma (ensures (let ss' = sseq_prefix ss i in
                    let s = index ss i in
                    let e = telem s in
                    ss == sseq_extend ss' e i))
  = let ss' = sseq_prefix ss i in
    let s = index ss i in
    let e = telem s in
    let s' = index ss' i in
    assert(s' = hprefix s);
    lemma_hprefix_append_telem s;
    assert(s = append1 s' e);
    let ss2 = sseq_extend ss' e i in

    let aux (t:_)
      : Lemma (ensures (index ss t = index ss2 t))
      = ()
    in
    FStar.Classical.forall_intro aux;
    assert(equal ss ss2)

let sseq_prefix_flatlen (#a:eqtype) (ss: sseq a) (i: seq_index ss{length (index ss i) > 0})
  : Lemma (ensures (let ss' = sseq_prefix ss i in
                    flat_length ss = flat_length ss' + 1))
  = let ss' = sseq_prefix ss i in
    let s = index ss i in
    let e = telem s in
    sseq_prefix_append ss i;
    lemma_sseq_extend_len ss' e i

open Zeta.SeqIdx

let nonzero_flatlen_implies_nonempty (#a:_) (ss: sseq a)
  : Lemma (ensures (flat_length ss > 0 ==> (exists i. (length (index ss i)) > 0)))
  = let n = length ss in
    let sse = empty a n in
    if flat_length ss > 0 then (
      let p = fun (s: seq a) -> length s > 0 in
      if not (exists_elems_with_prop_comp p ss) then (
        let aux ()
          : Lemma (ensures (ss == sse))
          = let aux2(t:_)
              : Lemma (ensures (index ss t == index sse t))
              = assert(length (index ss t) = 0);
                lemma_empty (index ss t)
            in
            FStar.Classical.forall_intro aux2;
            assert(equal ss sse)
        in
        aux()
      )
   )


let rec sum_count_empty (#a:eqtype) (s:sseq a) (x:a)
  : Lemma 
    (ensures 
      (forall (i:SeqAux.seq_index s).  Seq.index s i `Seq.equal` Seq.empty) ==>
      sum_count x s == 0)
    (decreases (Seq.length s))
  = if Seq.length s = 0 then () else sum_count_empty (fst (Seq.un_snoc s)) x

#push-options "--query_stats --fuel 1 --ifuel 1 --z3rlimit_factor 4"
let rec sum_count_i (#a:eqtype) (x:a) (ss:sseq a) (i:SeqAux.seq_index ss)
  : Lemma 
     (ensures sum_count x ss == sum_count x (Seq.upd ss i Seq.empty) + Seq.count x (Seq.index ss i))
     (decreases (Seq.length ss))
  = if i = Seq.length ss - 1
    then ()
    else (
      let prefix, last = Seq.un_snoc ss in
      calc (==) {
        sum_count x ss;
      (==) {}
        sum_count x prefix + Seq.count x last;
      (==) { sum_count_i x prefix i }
        sum_count x (Seq.upd prefix i Seq.empty) + Seq.count x (Seq.index prefix i) + Seq.count x last;
      (==) { 
             assert (Seq.equal (Seq.upd ss i Seq.empty) (Seq.upd (Seq.snoc prefix last) i Seq.empty))
           }
        sum_count x (Seq.upd ss i Seq.empty) + Seq.count x (Seq.index prefix i);
      }
    )


let sum_count_sseq_prefix (#a:eqtype) (ss:sseq a) (i: seq_index ss{length (Seq.index ss i) > 0}) (x:a)
  : Lemma (sum_count x ss == sum_count x (sseq_prefix ss i) + 
                             (if x = Seq.last (Seq.index ss i) then 1 else 0))
  = let si = Seq.index ss i in
    let si_prefix = SeqAux.prefix si (Seq.length si - 1) in
    let si_last = Seq.last si in
    calc (==) {
      sum_count x ss;
    (==) { sum_count_i x ss i }
      sum_count x (Seq.upd ss i Seq.empty) + Seq.count x si;
    (==) { assert (Seq.equal (Seq.upd ss i Seq.empty)
                             (Seq.upd (sseq_prefix ss i) i Seq.empty)) }
      sum_count x (Seq.upd (sseq_prefix ss i) i Seq.empty) + Seq.count x si;
    (==) {
           assert (si `Seq.equal` Seq.snoc si_prefix si_last);
           SeqAux.count_snoc si_prefix si_last x
         }
      sum_count x (Seq.upd (sseq_prefix ss i) i Seq.empty) + Seq.count x si_prefix + (if x = si_last then 1 else 0);
    };
    sum_count_i x (sseq_prefix ss i) i
    
#pop-options
