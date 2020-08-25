module Veritas.Interleave

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
  Lemma (append s1 s2 == append1 (append s1 (hprefix s2)) (telem s2)) = admit()

let lemma_hprefix_append1 (#a:Type) (s: seq a{length s > 0}):
  Lemma (s == append1 (hprefix s) (telem s)) = admit()

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

type interleave (#a:eqtype): seq a -> ss:sseq a -> Type0 = 
  | IntEmpty: interleave (empty #a) (empty #(seq a))
  | IntAdd: s:seq a -> ss: sseq a -> prf:interleave s ss -> interleave s (append1 ss (empty #a))
  | IntExtend: s:seq a -> ss: sseq a -> prf:interleave s ss -> x:a -> i:seq_index ss ->
               interleave (append1 s x) (sseq_extend ss x i)

  
