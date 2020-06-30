module Veritas.SeqOps

open FStar.Seq
open Veritas.SeqAux

val flat_length (#a:Type) (ss: seq (seq a)): Tot nat

(* append a single element to the end of a sequence *)
let append1 (#a:eqtype) (s:seq a) (x:a): s':(seq a){length s' = length s + 1} = 
  append s (create 1 x)

(* append a single element to the i'th seq in a sequence of sequences *)
let append1seq (#a:eqtype)
               (ss: seq (seq a)) 
               (x:a) (i:seq_index ss) =
  let si = index ss i in
  let si' = append1 si x in
  upd ss i si'

(*
 * interleave s [s0 s1 ... sp-1] represents that 
 * s is an interleaving of sequences s0 ... sp-1
 *)
type interleave (#a:eqtype) (#p:pos): seq a -> ss:(seq (seq a)){length ss = p} -> Type =  
  | IntEmpty: interleave #a #p (empty #a) (create p (empty #a))
  | IntAdd: s:seq a -> ss:(seq (seq a)){length ss = p} -> prf: interleave #a #p s ss 
                    -> x:a -> i:nat{i < p} 
                    -> interleave #a #p (append1 s x) (append1seq #a ss x i)     

#push-options "--print_universes --print_implicits"

(* map every element of the interleaved sequence to its source *)
val interleave_map (#a:eqtype) 
                   (#p:pos) 
                   (s:seq a) 
                   (ss: seq (seq a){length ss = p}) 
                   (prf: interleave #a #p s ss)
                   (i:seq_index s): 
  Tot (j:(nat*nat){fst j < p /\ 
            snd j < length (index ss (fst j)) /\
            index (index ss (fst j)) (snd j) = index s i} )

val interleave_inv_map (#a:eqtype)
                       (#p:pos)
                       (s:seq a)
                       (ss: seq (seq a){length ss = p})
                       (prf:interleave #a #p s ss)
                       (j:(nat*nat){fst j < p /\ 
                                  snd j < length (index ss (fst j))}): 
    Tot (i:(seq_index s){index (index ss (fst j)) (snd j) = index s i})

(* partition a sequence into independent sequences based on a partition function pf *)
val partition (#a:eqtype) (#p:pos) (s:seq a) (pf: a -> (i:nat{i < p})): 
  ss:seq (seq a){length ss = p /\ interleave #a #p s ss}

(* sortedness of a sequence *)
type sorted (#a:eqtype) (lte: a -> a -> bool) (s: seq a)  = 
  forall (i:seq_index s). i > 0 ==> index s (i - 1) `lte` index s i

(* type of a sequence of sequences where each individual sequence is sorted *)
type all_sorted (#a:eqtype) (lte: a -> a -> bool) (ss: seq (seq a)) = 
  forall (i: seq_index ss). sorted #a lte (index ss i)

(* merged interleaving of a sequence of sorted sequences *)
val merge_interleave (#a:eqtype) (lte: a -> a -> bool) 
                     (ss: seq (seq a) {all_sorted #a lte ss /\ length ss > 0}):
  s:seq a {interleave #a #(length ss) s ss /\ sorted #a lte s} 
