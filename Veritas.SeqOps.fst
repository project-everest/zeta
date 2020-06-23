module Veritas.SeqOps 

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
