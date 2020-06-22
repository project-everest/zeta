module Veritas.SeqOps

open FStar.Seq

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


