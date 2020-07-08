module Veritas.Interleave

open FStar.Seq
open Veritas.SeqAux

(* interleaving of n sequences *)
val interleave (#a:eqtype): seq a -> ss:(seq (seq a)) -> Type 

(* if we have a proof of interleaving we can construct a mapping from 
 * interleaved sequence to the sources *)
val interleave_map (#a:eqtype) (s: seq a) (ss: seq (seq a)) 
     (prf:interleave #a s ss) (i: seq_index s): 
  Tot (j: (nat*nat){fst j < length ss /\
                 snd j < length (index ss (fst j)) /\
                 index (index ss (fst j)) (snd j) = index s i})

(* inverse of interleave map *)
val interleave_map_inv (#a:eqtype) (s: seq a) (ss: seq (seq a))
      (prf:interleave #a s ss) (i: seq_index ss) (j: seq_index (index ss i)): 
  Tot (k: seq_index s{index s k = index (index ss i) j})

(* sortedness of a sequence *)
type sorted (#a:Type) (lte: a -> a -> bool) (s: seq a) = 
  forall (i:seq_index s). i > 0 ==> index s (i - 1) `lte` index s i

(* sort-merge interleaving *)
val sort_merge (#a:eqtype) (lte: a-> a-> bool) 
               (ss: seq (seq a){forall (i:seq_index ss). sorted lte (index ss i)}): 
  s:(seq a){interleave s ss /\ sorted lte s} 
    
