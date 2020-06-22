module Veritas.SeqOps

open FStar.Seq
open Veritas.SeqAux

(* append a single element to the end of a sequence *)
let append1 (#a:eqtype) (s:seq a) (x:a): s':(seq a){length s' = length s + 1} = 
  append s (create 1 x)

(* append a single element to the i'th seq in a sequence of sequences *)
let append1seq (#a:eqtype) (#p:pos) 
               (ss: (seq (seq a)){length ss = p}) 
               (x:a) (i:nat{i < p}) =
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
                    -> interleave #a #p (append1 s x) (append1seq #a #p ss x i)     

(* map every element of the interleaved sequence to its source *)
let interleave_map (#a:eqtype) 
                   (#p:pos) 
                   (s:seq a) 
                   (ss: seq (seq a){length ss = p}) 
                   (prf: interleave #a #p s ss)
                   (i:seq_index s): 
  j:(nat*nat){fst j < p /\ 
            snd j < length (index ss (fst j)) /\
            index (index ss (fst j)) (snd j) = index s i} = 
  match prf with
  | IntEmpty -> assert(s == empty #a); (0,0)
  | IntAdd s' ss' prf' x i' -> assert(s == append1 s' x);
                               assert(i <= length s');
                               if i = length s then (
                                 let si'' = index ss' i' in
                                 let si' = index ss i' in
                                 assert(si' == append1 si'' x);
                                 
                                 admit()
                               )
                               else
                                 admit()
