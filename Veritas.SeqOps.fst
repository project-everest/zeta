module Veritas.SeqOps 

#push-options "--print_implicits --print_universes"

type interleave (#a:eqtype): seq a -> seq a -> seq a -> Type =
  | IntEmpty: interleave #a (empty #a) (empty #a) (empty #a)
  | IntLeft: s: seq a -> s1: seq a 
                      -> s2: seq a 
                      -> prf: interleave s s1 s2 
                      -> x:a 
                      -> interleave (append1 s x) (append1 s1 x) s2
  | IntRight: s: seq a -> s1: seq a 
                       -> s2: seq a 
                       -> prf:interleave s s1 s2 
                       -> x:a
                       -> interleave (append1 s x) s1 (append1 s x)


// open Veritas.SeqAux

(*

let rec flat_length_aux (#a:Type) (ss: seq (seq a)): Tot nat (decreases (length ss)) = 
  let n = length ss in
  if n = 0 then 0
  else
    let ss' = prefix ss (n - 1) in
    let s = index ss (n - 1) in
    flat_length_aux ss' + length s
    
let flat_length (#a:Type) (ss: seq (seq a)): Tot nat = flat_length_aux ss

let rec interleave_map_aux (#a:eqtype) 
                   (#p:pos) 
                   (s:seq a) 
                   (ss: seq (seq a){length ss = p}) 
                   (prf: interleave #a #p s ss)
                   (i:seq_index s): 
  Tot (j:(nat*nat){fst j < p /\ 
            snd j < length (index ss (fst j)) /\
            index (index ss (fst j)) (snd j) = index s i} )
  (decreases prf)
            = 
  match prf with
  | IntEmpty -> assert(s == empty #a); (0,0)
  | IntAdd s' ss' prf' x i' -> if i = length s' then 
                                 (i', length (index ss' i'))                               
                               else
                                 interleave_map_aux s' ss' prf' i

let interleave_map (#a:eqtype) 
                   (#p:pos) 
                   (s:seq a) 
                   (ss: seq (seq a){length ss = p}) 
                   (prf: interleave #a #p s ss)
                   (i:seq_index s): 
  Tot (j:(nat*nat){fst j < p /\ 
            snd j < length (index ss (fst j)) /\
            index (index ss (fst j)) (snd j) = index s i} ) = 
  interleave_map_aux s ss prf i

let rec interleave_inv_map_aux (#a:eqtype)
                       (#p:pos)
                       (s:seq a)
                       (ss: seq (seq a){length ss = p})
                       (prf:interleave #a #p s ss)
                       (j:(nat*nat){fst j < p /\ 
                                  snd j < length (index ss (fst j))}): 
  Tot (i:(seq_index s){index (index ss (fst j)) (snd j) = index s i}) 
  (decreases prf)
  = 
  match prf with
  | IntEmpty -> 0
  | IntAdd s' ss' prf' x i' -> let p,q = j in
                               let si' = index ss' i' in
                               if p = i' && q = length si' then
                                 length s'
                               else
                                 interleave_inv_map_aux s' ss' prf' j

let interleave_inv_map (#a:eqtype)
                       (#p:pos)
                       (s:seq a)
                       (ss: seq (seq a){length ss = p})
                       (prf:interleave #a #p s ss)
                       (j:(nat*nat){fst j < p /\ 
                                  snd j < length (index ss (fst j))}): 
  Tot (i:(seq_index s){index (index ss (fst j)) (snd j) = index s i}) = 
  interleave_inv_map_aux s ss prf j

let partition_aux (#a:eqtype) (#p:pos) (s:seq a) (pf: a -> (i:nat{i < p})): 
  ss:seq (seq a){length ss = p /\ interleave #a #p s ss} = admit()

(* partition a sequence into independent sequences based on a partition function pf *)
let partition (#a:eqtype) (#p:pos) (s:seq a) (pf: a -> (i:nat{i < p})): 
  ss:seq (seq a){length ss = p /\ interleave #a #p s ss} = partition_aux #a #p s pf

let merge_interleave (#a:eqtype) (lte: a -> a -> bool) 
                     (ss: seq (seq a) {all_sorted #a lte ss /\ length ss > 0}):
  s:seq a {interleave #a #(length ss) s ss /\ sorted #a lte s}  = admit()
*)
