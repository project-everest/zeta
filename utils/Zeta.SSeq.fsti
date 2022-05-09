module Zeta.SSeq

open FStar.Seq
open Zeta.SeqAux

(* sequence of sequences *)
type sseq (a:Type) = seq (seq a)

(* an index into an element of sseq *)
type sseq_index (#a:Type) (ss: sseq a) =
  (ij:(nat * nat){(fst ij) < length ss /\
               (snd ij) < length (index ss (fst ij))})

(* retrieve an element of an sseq given its index *)
let indexss (#a:Type) (ss: sseq a) (ij: sseq_index ss): Tot a =
  let (i,j) = ij in
  index (index ss i) j

(* sum of lengths of all sequences in a sequence of seqs *)
val flat_length (#a:Type) (ss: sseq a)
  : Tot nat

(* flat length of an empty sseq *)
val lemma_flat_length_empty (#a:Type)
  : Lemma (flat_length (empty #(seq a)) = 0)

(* appending a singleton adds to the flat length *)
val lemma_flat_length_app1 (#a:Type) (ss: sseq a) (s: seq a)
  : Lemma (flat_length ss + length s = flat_length (append1 ss s))

(* appending adds to the flat length *)
val lemma_flat_length_app (#a:Type) (ss1 ss2: sseq a)
  : Lemma (flat_length ss1 + flat_length ss2 = flat_length (append ss1 ss2))

let sseq_extend (#a:eqtype) (ss: sseq a) (x:a) (i:seq_index ss): sseq a =
  let si = index ss i in
  let si' = append1 si x in
  upd ss i si'

val lemma_sseq_correct1 (#a:eqtype) (ss: sseq a) (x:a) (i:seq_index ss):
  Lemma (index (sseq_extend ss x i) i = append1 (index ss i) x)

val lemma_sseq_correct2 (#a:eqtype) (ss: sseq a) (x:a) (i:seq_index ss) (j:seq_index ss{j <> i}):
  Lemma (index (sseq_extend ss x i) j = index ss j)

val lemma_sseq_extend_len (#a:eqtype) (ss: sseq a) (x:a) (i:seq_index ss):
  Lemma (ensures (flat_length (sseq_extend ss x i) = 1 + flat_length ss))

let sseq_all_prefix_of (#a:eqtype)
                       (ss0 ss1: sseq a)
  = length ss0 = length ss1 /\
    (forall (tid:seq_index ss1). (index ss0 tid) `prefix_of` (index ss1 tid))

let empty (a:_) (n:nat)
  : sseq a
  = create n (empty #a)

val lemma_flat_length_emptyn (a:_) (n:nat)
  : Lemma (ensures (flat_length (empty a n) = 0))
          [SMTPat (empty a n)]

val lemma_flat_length_zero (#a:_) (ss: sseq a {flat_length ss = 0})
  : Lemma (ensures (ss == empty a (length ss)))

let sseq_prefix (#a:eqtype) (ss: sseq a) (i: seq_index ss{length (index ss i) > 0})
  = let s = index ss i in
    let l = length s in
    let s' = prefix s (l - 1) in
    upd ss i s'

val sseq_prefix_flatlen (#a:eqtype) (ss: sseq a) (i: seq_index ss{length (index ss i) > 0})
  : Lemma (ensures (let ss' = sseq_prefix ss i in
                    flat_length ss = flat_length ss' + 1))
          [SMTPat (sseq_prefix ss i)]

val nonzero_flatlen_implies_nonempty (#a:_) (ss: sseq a)
  : Lemma (ensures (flat_length ss > 0 ==> (exists i. (length (index ss i)) > 0)))


let rec sum_count (#a:eqtype) (x:a) (s:sseq a)
  : Tot nat (decreases (Seq.length s))
  = if Seq.length s = 0 then 0
    else let prefix, last = Seq.un_snoc s in
         Seq.count x last + sum_count x prefix

val sum_count_empty (#a:eqtype) (s:sseq a) (x:a)
  : Lemma 
    (ensures 
      (forall (i:SeqAux.seq_index s).  Seq.index s i `Seq.equal` Seq.empty) ==>
      sum_count x s == 0)

val sum_count_i (#a:eqtype) (x:a) (ss:sseq a) (i:SeqAux.seq_index ss)
  : Lemma 
     (ensures sum_count x ss == sum_count x (Seq.upd ss i Seq.empty) + Seq.count x (Seq.index ss i))

val sum_count_sseq_prefix (#a:eqtype) (ss:sseq a) (i: seq_index ss{length (Seq.index ss i) > 0}) (x:a)
  : Lemma (sum_count x ss == sum_count x (sseq_prefix ss i) + 
                             (if x = Seq.last (Seq.index ss i) then 1 else 0))
